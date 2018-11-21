/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following.  Be sure not
 * to have debugging enabled in your final submission
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__) 
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif



/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */


/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

/* What is the correct alignment? */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    struct block* prev;
    struct block* next;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

#define LIST_NUM  7
static block_t *free_listp_array[LIST_NUM];
static block_t *free_listp_array_tail[LIST_NUM];
// static size_t lines[LIST_NUM] = {1, 70, 150, 300, 840, 1800};
// static block_t *best_fit;

/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
// static block_t *free_listp;
// static block_t *free_listp_2;
/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

bool mm_checkheap(int lineno);

static void remove_free_block(block_t* pointer);
static void insert_free_block(block_t* pointer);
static int explict_list_check(int lineno, int explict_list_check);
static int get_number(size_t size);



/*
 * mm_init: initializes the heap; it is run once when heap_start == NULL.
 *          prior to any extend_heap operation, this is the heap:
 *              start            start+8           start+16
 *          INIT: | PROLOGUE_FOOTER | EPILOGUE_HEADER |
 * heap_listp ends up pointing to the epilogue header.
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }
    
    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) &(start[1]);

    for (int i = 0; i < LIST_NUM; i++) {
        free_listp_array[i] = NULL;
        free_listp_array_tail[i] = NULL;
    }
    block_t* mm_init_block = extend_heap(chunksize);
    if (mm_init_block == NULL)
    {
        return false;
    }
    dbg_printf("mm_init_block: %p\n", mm_init_block);
    dbg_printf("mm_init's pointer's header: %lu\n", mm_init_block->header);
    return true;
}

/*
 * malloc: allocates a block with size at least (size + dsize), rounded up to
 *         the nearest 16 bytes, with a minimum of 2*dsize. Seeks a
 *         sufficiently-large unallocated block on the heap to be allocated.
 *         If no such block is found, extends heap by the maximum between
 *         chunksize and (size + dsize) rounded up to the nearest 16 bytes,
 *         and then attempts to allocate all, or a part of, that memory.
 *         Returns NULL on failure, otherwise returns a pointer to such block.
 *         The allocated block will not be used for further allocations until
 *         freed.
 */
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap);
    
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }
    dbg_printf("input size: %lu\n", size);
    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap);
        return bp;
    }
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size, dsize) + dsize;
    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);

        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_printf("Malloc size %zd on address %p.\n", size, bp);
    dbg_ensures(mm_checkheap);
    return bp;
} 

/*
 * free: Frees the block such that it is no longer allocated while still
 *       maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);

}
/*
 * realloc: returns a pointer to an allocated region of at least size bytes:
 *          if ptrv is NULL, then call malloc(size);
 *          if size == 0, then call free(ptr) and returns NULL;
 *          else allocates new region of memory, copies old data to new memory,
 *          and then free old block. Returns old block if realloc fails or
 *          returns new pointer on success.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc: Allocates a block with size at least (elements * size + dsize)
 *         through malloc, then initializes all bits in allocated memory to 0.
 *         Returns NULL on failure.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    dbg_printf("extend_heap start: before ini free block header and footers\n");
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    dbg_printf("examine next block header\n");
    dbg_printf("header: %lu\n", block_next->header);
    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalesce: Coalesces current block with previous and next blocks if either
 *           or both are unallocated; otherwise the block is not modified.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);

    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
        // dbg_printf("case1\n");
        insert_free_block(block);
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        // dbg_printf("case2\n");
        size += get_size(block_next);
        remove_free_block(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        // dbg_printf("case3\n");
        size += get_size(block_prev);
        remove_free_block(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
    }

    else                                     // Case 4
    {
        // dbg_printf("case4\n");
        remove_free_block(block_prev);
        remove_free_block(block_next);
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
    }
    insert_free_block(block);   
    return block;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    remove_free_block(block);
    
    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);

        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);

        coalesce(block_next);
    }

    else
    { 
        write_header(block, csize, true);
        write_footer(block, csize, true);
    }
}

static int get_number(size_t size) {
    if (size < 64) {
        return 0;
    }
    else if (size < 128) {
        return 1;
    }
    else if (size < 240) {
        return 2;
    }
    if (size < 430) {
        return 3;
    }
    if (size < 800) {
        return 4;
    }
    else if (size < 1500){
        return 5;
    } 
    else {
        return 6;
    }
} 
/*
 * find_fit: Looks for a free block with at least asize bytes with
 *           first-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    dbg_printf("entering find_fit\n");
    block_t *block;

    int count = 0;
    block_t *best_fit = NULL;
    for (int i = get_number(asize); i < LIST_NUM; ++i) {
        for (block = free_listp_array_tail[i]; block != NULL; block = block->prev) {
            if ((asize <= get_size(block))) {
                count++;
                if (count == 1) {
                    best_fit = block;
                } else if (get_size(block) < get_size(best_fit)) {
                    best_fit = block;
                }
                return best_fit;
            }
        }
    }

    dbg_printf("block : %p\n", block);
    return NULL; // no fit found
}

/*
 * remove free blocks in from the free list
 */
static void remove_free_block(block_t* pointer) {
    dbg_printf("remove address: %p\n", pointer);

    block_t* block_prev = pointer->prev;
    block_t* block_next = pointer->next;

    int free_list_number = get_number(get_size(pointer));

    /* case 1: remove block when there is only one block in the list */
    if (block_prev == NULL && block_next == NULL) {
        free_listp_array[free_list_number] = NULL;
        free_listp_array_tail[free_list_number] = NULL;
    } 
    /* Case 2: remove the top element of the list*/
    else if (block_prev == NULL && block_next != NULL) {
        free_listp_array[free_list_number] = block_next;
        free_listp_array[free_list_number]->prev = NULL;
    }
    /*Case 3: remove the last element of the list */
    else if (block_prev != NULL && block_next == NULL) {
        free_listp_array_tail[free_list_number] = block_prev;
        block_prev->next = NULL;
    }
    /*Case 4: remove the element in the middle*/
    else {
        block_prev->next = block_next;
        block_next->prev = block_prev;
    }
}

static void insert_free_block(block_t* pointer) {
    int free_list_number = get_number(get_size(pointer));

    if (free_listp_array[free_list_number] == NULL) {
        free_listp_array[free_list_number] = pointer;
        free_listp_array_tail[free_list_number] = pointer;
        pointer->prev = NULL;
        pointer->next = NULL;
        return;
    }
    pointer->prev = NULL;
    pointer->next = free_listp_array[free_list_number];
    free_listp_array[free_list_number]->prev = pointer;
     /* update the free_listp */
    free_listp_array[free_list_number] = pointer;

}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    // dbg_printf("entering round_up\n");
    // size_t return_value = (n * ((size + (n-1)) / n));
    // dbg_printf("size: round_up value is: %lu\n", return_value);
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | 1) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) - 16 + get_size(block) - dsize);  /* pay attention to 16 and char() */ // <Important>
    *footerp = pack(size, alloc);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, prev));/* change block_t, payload to block_t prev */ //<Important>//
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload - 16); /* change block->payload to block->prev */ //<Important>//
}

/*
 * address starts at 0x80000000,and it is 16 bytes alignment
 */
static bool check_aligned(void* p, int lineno) {
    size_t ip = (size_t) p;
    if (align(ip) != ip) {
        dbg_printf("Address: %p payload address alignment falied in lineno: %d\n", p,lineno);
        return false;
    } else {
        return true;
    }
}

static bool check_in_heap(const void* bp, int lineno) {
    if (bp <= mem_heap_hi() && bp >= mem_heap_lo()) {
        return true;
    } else {
        dbg_printf("Address: %p: payload pointer not in the heap in lineno: %d\n",bp, lineno);
        return false;
    }
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int lineno)  
{       
    /* Check prologue */ 
    if (get_size(heap_listp) != min_block_size || get_alloc(heap_listp)) {
        dbg_printf("Address: %p is Prologue Error \n", heap_listp);
        return false;
    }
    if (heap_listp == NULL) {
        dbg_printf("Address: %p : is null in lineno: %d\n", heap_listp, lineno);
        return false;
    }

    int implicit_free_count = 0;
    int explicit_free_count = 0;

    block_t* block_prev = heap_listp;
    block_t* block_next;

    word_t* footer_prev;
    word_t* header_prev;

    void* payload_prev;

    size_t size_prev;

    while (get_size(block_prev) != 0) {
        dbg_printf("entering while loop in heap check\n");
        header_prev = &(block_prev->header);
        block_next = find_next(block_prev);
        footer_prev = find_prev_footer(block_next);
        payload_prev = header_to_payload(block_prev);

        /* check block address alignment */
        if (check_aligned(payload_prev, lineno) == false) {
            return false;
        }
        /* check if the payload pointer in heap */
        if (check_in_heap((void *)payload_prev, lineno) == false) {
            return false;
        }
        /* check min size */
        size_prev = get_size(block_prev);
        if (get_alloc(block_prev) == true) {
            if (size_prev < min_block_size) {
                printf("Address: %p : minimum block size requirement not satisfied in lineno: %d\n", payload_prev, lineno);
                return false;
            }
        }
        // size match in header and payload 
        if (extract_size(*header_prev) != size_prev) {
            printf("Address: %p : size in header unmatch block size in lineno: %d\n", payload_prev, lineno);
            return false;
        }
        if (extract_alloc(*header_prev) != get_alloc(block_prev)) {
            printf("Address: %p: allocate/free bit in one block unmatch in lineno: %d\n",payload_prev, lineno);
            return false;
        }
        /* check footer header alignment */
        if (size_prev % ALIGNMENT != 0) {
            printf("Address: %p: Header footer not Double-Word Aligned in lineno: %d\n", payload_prev, lineno);
            return false;
        }
        /* check header footer match */
        if (*footer_prev != *header_prev) {
            dbg_printf("Address: %p: Footer and Header unmatch in lineno: %d\n", payload_prev,lineno);
            return false;
        }

        /* check coalesce */
        if (get_alloc(block_prev) == false && get_alloc(block_next) == false) {
            dbg_printf("two consecutive free blocks in the heap in lineno: %d\n", lineno);
            return false;
        }
        if (get_alloc(block_prev) == false) {
            implicit_free_count++;
        }
        block_prev = block_next;
    }

    explicit_free_count = explict_list_check(lineno, explicit_free_count);
    /* check if both free-counts are equal */
    if (explicit_free_count != implicit_free_count) {
        dbg_printf("explicit_free_count is not equal to implicit_free_count\n");
        return false;
    }
    dbg_printf("normally exit heap check\n");
    return true;
}

static int explict_list_check(int lineno, int explicit_free_count) {
    dbg_printf("entering explicit list check\n");
    block_t *pointer = free_listp_array[0];

    if (free_listp_array[0] == NULL) {
        dbg_printf("free_listp is NULL\n");
        return explicit_free_count;
    }
    while (pointer != NULL) {
        if (pointer->next != NULL && pointer->prev != NULL) {
            if (pointer->prev->next != pointer->next->prev) {
                dbg_printf("Address: %p: next/prev not consistent in lineno: %d\n",pointer, lineno);
                return explicit_free_count;
            }
        }
        if (check_in_heap((void *)pointer, lineno) == false) {
            return explicit_free_count;
        }
        explicit_free_count++;
        pointer = pointer->next;
    }
    dbg_printf("normally exit explict_list_check\n");
    return explicit_free_count;
}

