/*
 * This file is part of AtomVM.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

/*
 * cjson:decode/1 -- JSON text to terms, parsed natively with cJSON.
 *
 * Returns what json:decode/1 does: objects are maps with binary keys,
 * arrays are lists, strings are binaries, and true, false and null are
 * atoms. Numbers go through a double: an integral one within 2^53 comes
 * back as an integer (so 1.0 decodes as 1), anything else as a float.
 * A duplicated key keeps its last value. Invalid JSON raises badarg.
 *
 * cJSON allocates a node per value; its allocator is pointed at PSRAM so
 * those small blocks stay out of internal RAM.
 *
 * cjson:decode/2 takes a list of binary keys and keeps only object members
 * with one of those keys, at any depth. What it drops is pruned from the
 * cJSON tree before any term is built, so a string that is never wanted
 * never becomes a binary; one over 64 bytes would be a refc binary, and
 * those up to 512 bytes come from internal RAM.
 */

#include <sdkconfig.h>
#ifdef CONFIG_AVM_ENABLE_CJSON_NIFS

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <cJSON.h>
#include <esp_heap_caps.h>

#include <atom.h>
#include <defaultatoms.h>
#include <globalcontext.h>
#include <interop.h>
#include <memory.h>
#include <nifs.h>
#include <portnifloader.h>
#include <term.h>

//#define ENABLE_TRACE
#include "trace.h"

#define MAX_DEPTH 64
#define MAX_KEYS 32
#define MAX_KEY_LENGTH 32

struct Filter
{
    int count;
    char keys[MAX_KEYS][MAX_KEY_LENGTH + 1];
};
#define MAX_EXACT_DOUBLE 9007199254740992.0

struct Key
{
    cJSON *item;
    int index;
};

static void *cjson_malloc(size_t size)
{
    void *ptr = heap_caps_malloc(size, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
    return ptr != NULL ? ptr : malloc(size);
}

static void cjson_free(void *ptr)
{
    free(ptr);
}

static bool is_integral(double value)
{
    return value >= -MAX_EXACT_DOUBLE && value <= MAX_EXACT_DOUBLE
        && value == (double) (avm_int64_t) value;
}

static int compare_keys(const void *a, const void *b)
{
    const struct Key *x = a;
    const struct Key *y = b;
    int result = strcmp(x->item->string, y->item->string);
    if (result != 0) {
        return result;
    }
    return x->index - y->index;
}

// Sorts an object's members by key, as maps require, keeping the last of any duplicates.
static bool sort_object(cJSON *object)
{
    int count = 0;
    for (cJSON *child = object->child; child != NULL; child = child->next) {
        count++;
    }
    if (count < 2) {
        return true;
    }

    struct Key *keys = cjson_malloc(count * sizeof(struct Key));
    if (IS_NULL_PTR(keys)) {
        return false;
    }
    int i = 0;
    for (cJSON *child = object->child; child != NULL; child = child->next) {
        keys[i].item = child;
        keys[i].index = i;
        i++;
    }
    qsort(keys, count, sizeof(struct Key), compare_keys);

    cJSON *head = NULL;
    cJSON *tail = NULL;
    for (i = 0; i < count; i++) {
        cJSON *item = keys[i].item;
        if (i + 1 < count && strcmp(item->string, keys[i + 1].item->string) == 0) {
            item->next = NULL;
            item->prev = NULL;
            cJSON_Delete(item);
            continue;
        }
        item->next = NULL;
        if (head == NULL) {
            head = item;
        } else {
            tail->next = item;
            item->prev = tail;
        }
        tail = item;
    }
    head->prev = tail;
    object->child = head;

    cjson_free(keys);
    return true;
}

static bool wanted(const struct Filter *filter, const char *key)
{
    for (int i = 0; i < filter->count; i++) {
        if (strcmp(filter->keys[i], key) == 0) {
            return true;
        }
    }
    return false;
}

// Drops the members of an object whose keys the filter does not name.
static void prune_object(cJSON *object, const struct Filter *filter)
{
    cJSON *child = object->child;
    while (child != NULL) {
        cJSON *next = child->next;
        if (!wanted(filter, child->string)) {
            cJSON_Delete(cJSON_DetachItemViaPointer(object, child));
        }
        child = next;
    }
}

// Prunes and sorts every object and counts the heap words the terms will take.
static bool prepare(cJSON *node, const struct Filter *filter, int depth, size_t *size)
{
    if (depth > MAX_DEPTH) {
        return false;
    }

    switch (node->type & 0xFF) {
        case cJSON_False:
        case cJSON_True:
        case cJSON_NULL:
            return true;

        case cJSON_Number:
            if (is_integral(node->valuedouble)) {
                *size += term_boxed_integer_size((avm_int64_t) node->valuedouble);
            } else {
                *size += FLOAT_SIZE;
            }
            return true;

        case cJSON_String:
            *size += term_binary_heap_size(strlen(node->valuestring));
            return true;

        case cJSON_Array:
            for (cJSON *child = node->child; child != NULL; child = child->next) {
                *size += CONS_SIZE;
                if (!prepare(child, filter, depth + 1, size)) {
                    return false;
                }
            }
            return true;

        case cJSON_Object: {
            if (filter != NULL) {
                prune_object(node, filter);
            }
            if (!sort_object(node)) {
                return false;
            }
            size_t count = 0;
            for (cJSON *child = node->child; child != NULL; child = child->next) {
                count++;
                *size += term_binary_heap_size(strlen(child->string));
                if (!prepare(child, filter, depth + 1, size)) {
                    return false;
                }
            }
            *size += term_map_size_in_terms(count);
            return true;
        }

        default:
            return false;
    }
}

static term build(cJSON *node, term null_atom, Heap *heap, GlobalContext *glb)
{
    switch (node->type & 0xFF) {
        case cJSON_False:
            return FALSE_ATOM;

        case cJSON_True:
            return TRUE_ATOM;

        case cJSON_NULL:
            return null_atom;

        case cJSON_Number:
            if (is_integral(node->valuedouble)) {
                return term_make_maybe_boxed_int64((avm_int64_t) node->valuedouble, heap);
            }
            return term_from_float((avm_float_t) node->valuedouble, heap);

        case cJSON_String:
            return term_from_literal_binary(node->valuestring, strlen(node->valuestring), heap, glb);

        case cJSON_Array: {
            term list = term_nil();
            if (node->child == NULL) {
                return list;
            }
            // The head's prev is the tail, so the list is built back to front.
            cJSON *child = node->child->prev;
            while (true) {
                term value = build(child, null_atom, heap, glb);
                if (term_is_invalid_term(value)) {
                    return value;
                }
                list = term_list_prepend(value, list, heap);
                if (child == node->child) {
                    return list;
                }
                child = child->prev;
            }
        }

        case cJSON_Object: {
            int count = 0;
            for (cJSON *child = node->child; child != NULL; child = child->next) {
                count++;
            }
            term map = term_alloc_map(count, heap);
            int i = 0;
            for (cJSON *child = node->child; child != NULL; child = child->next) {
                term key = term_from_literal_binary(child->string, strlen(child->string), heap, glb);
                term value = build(child, null_atom, heap, glb);
                if (term_is_invalid_term(key) || term_is_invalid_term(value)) {
                    return term_invalid_term();
                }
                term_set_map_assoc(map, i, key, value);
                i++;
            }
            return map;
        }

        default:
            return term_invalid_term();
    }
}

// Copies a list of binary keys into a filter; false if it is not one or too long.
static bool read_filter(term list, struct Filter *filter)
{
    filter->count = 0;
    while (term_is_nonempty_list(list)) {
        term key = term_get_list_head(list);
        if (!term_is_binary(key) || filter->count == MAX_KEYS
            || term_binary_size(key) > MAX_KEY_LENGTH) {
            return false;
        }
        size_t length = term_binary_size(key);
        memcpy(filter->keys[filter->count], term_binary_data(key), length);
        filter->keys[filter->count][length] = '\0';
        filter->count++;
        list = term_get_list_tail(list);
    }
    return term_is_nil(list);
}

static term nif_cjson_decode(Context *ctx, int argc, term argv[])
{
    VALIDATE_VALUE(argv[0], term_is_binary);

    // On the stack: a filter is at most MAX_KEYS short keys.
    struct Filter filter;
    const struct Filter *keep = NULL;
    if (argc == 2) {
        if (!read_filter(argv[1], &filter)) {
            RAISE_ERROR(BADARG_ATOM);
        }
        keep = &filter;
    }

    const char *text = term_binary_data(argv[0]);
    size_t length = term_binary_size(argv[0]);

    const char *end = NULL;
    cJSON *root = cJSON_ParseWithLengthOpts(text, length, &end, false);
    if (IS_NULL_PTR(root)) {
        RAISE_ERROR(BADARG_ATOM);
    }
    // Only whitespace may follow the value.
    while (end < text + length && (*end == ' ' || *end == '\t' || *end == '\n' || *end == '\r')) {
        end++;
    }
    if (end != text + length) {
        cJSON_Delete(root);
        RAISE_ERROR(BADARG_ATOM);
    }

    size_t size = 0;
    if (!prepare(root, keep, 0, &size)) {
        cJSON_Delete(root);
        RAISE_ERROR(BADARG_ATOM);
    }

    // argv is not needed past this point, so a collection may move it.
    if (UNLIKELY(memory_ensure_free_opt(ctx, size, MEMORY_CAN_SHRINK) != MEMORY_GC_OK)) {
        cJSON_Delete(root);
        RAISE_ERROR(OUT_OF_MEMORY_ATOM);
    }

    term null_atom = globalcontext_make_atom(ctx->global, ATOM_STR("\x4", "null"));
    term result = build(root, null_atom, &ctx->heap, ctx->global);
    cJSON_Delete(root);

    if (term_is_invalid_term(result)) {
        RAISE_ERROR(OUT_OF_MEMORY_ATOM);
    }
    return result;
}

static const struct Nif cjson_decode_nif = {
    .base.type = NIFFunctionType,
    .nif_ptr = nif_cjson_decode
};

static void cjson_nif_init(GlobalContext *global)
{
    UNUSED(global);

    cJSON_Hooks hooks = {
        .malloc_fn = cjson_malloc,
        .free_fn = cjson_free
    };
    cJSON_InitHooks(&hooks);
}

static const struct Nif *cjson_nif_get_nif(const char *nifname)
{
    if (strcmp("cjson:decode/1", nifname) == 0 || strcmp("cjson:decode/2", nifname) == 0) {
        TRACE("Resolved platform nif %s ...\n", nifname);
        return &cjson_decode_nif;
    }
    return NULL;
}

REGISTER_NIF_COLLECTION(cjson, cjson_nif_init, NULL, cjson_nif_get_nif)

#endif
