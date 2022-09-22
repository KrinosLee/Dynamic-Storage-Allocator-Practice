/*
 * mm.c
 *
 * Name: Zerui Li and Qia Lin
 * Cited from textbook "Computer Systems A Programmer’s Perspective"
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. Krinos Qia lIN
 *
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
  * If you want to enable your debugging output and heap checker code,
  * uncomment the following line. Be sure not to have debugging enabled
  * in your final submission.
  */
  // #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16
#define MAX 0xFFFFFFFFFFFFFFFF
/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x + ALIGNMENT - 1) / ALIGNMENT);
}

typedef struct mem_block {
    size_t size, pre_size;
    struct mem_block* next_block, * pre_block;
}block;

block* last_block;
block* limit;
static size_t GetSize(block* this_block) {
    return (this_block->size) & (MAX - 1);
}
static size_t GetPreSize(block* this_block) {
    return (this_block->pre_size) & (MAX - 1);
}
static block* GetNextBlock(block* this_block) {
    return (block*)((unsigned char*)this_block + 16 + align(GetSize(this_block)));
}
static block* GetPreBlock(block* this_block) {
    return (block*)((unsigned char*)this_block - 16 - align(GetPreSize(this_block)));
}
static bool IsFree(block* this_block) {
    return this_block->size & 1;
}
static void SetFree(block* this_block) {
    this_block->size |= 1;
}
static void SetNoFree(block* this_block) {
    this_block->size &= (MAX - 1);
    this_block->next_block = this_block->pre_block= NULL;
}
static void DeleteBlock(block* this_block) {
    this_block->next_block = this_block->pre_block = NULL;
    this_block->pre_size = this_block->size = 0;
}

static block** GetFreeBlockHead(size_t size) {
    if (size <= 16)return (block**)mem_heap_lo();
    else if (size <= 32)return (block**)((unsigned char*)mem_heap_lo() + 8);
    //else if (size <= 64)return (block**)((unsigned char*)mem_heap_lo() + 16);
    //else if (size <= 128)return (block**)((unsigned char*)mem_heap_lo() + 24);
    //else if (size <= 512)return (block**)((unsigned char*)mem_heap_lo() + 32);
    //else if (size <= 2048)return (block**)((unsigned char*)mem_heap_lo() + 16);
    else if (size <= 4096)return (block**)((unsigned char*)mem_heap_lo() + 16);
    //else if (size <= 1024)return (block**)((unsigned char*)mem_heap_lo() + 56);
    //else if (size <= 2048)return (block**)((unsigned char*)mem_heap_lo() + 64);
    else return (block**)((unsigned char*)mem_heap_lo() + 24);
}

static void* GetPtr(block* this_block) {
    return (void*)((unsigned char*)this_block + 16);
}

static block* GetHead(void* ptr) {
    return (block*)((unsigned char*)ptr - 16);
}

static void OutFreeList(block* this_block) {
    /*if (this_block->pre_block >= limit) {
        this_block->pre_block->next_block = this_block->next_block;
        if (this_block->next_block)
            this_block->next_block->pre_block = this_block->pre_block;
    }*/
    block** head = GetFreeBlockHead(GetSize(this_block));
    if (!this_block->pre_block) {//this_block->pre_block==NULL即为头指向
        if (this_block->next_block) {
            *head = this_block->next_block;
            this_block->next_block->pre_block = NULL;
        }
        else *head = NULL;
    }
    else {
        this_block->pre_block->next_block = this_block->next_block;
        if (this_block->next_block)
            this_block->next_block->pre_block = this_block->pre_block;
    }
    SetNoFree(this_block);
}

static void InFreeList(block* this_block) {
    block** head = GetFreeBlockHead(GetSize(this_block));
    SetFree(this_block);
    if (*head) {
        block* p = *head;
        for (; p->next_block && GetSize(p) < GetSize(this_block); p = p->next_block);
        if (p->next_block) {
            p->next_block->pre_block = this_block;
            this_block->next_block = p->next_block;
            p->next_block = this_block;
            this_block->pre_block = p;
        }
        else {
            p->next_block = this_block;
            this_block->pre_block = p;
            this_block->next_block = NULL;
        }
        /*this_block->next_block = *head;
        (*head)->pre_block = this_block;
        *head = this_block;
        this_block->pre_block = NULL;*/
    }
    else {
        *head = this_block;
        this_block->pre_block = this_block->next_block = NULL;
    }
}
static void FuseBlock(block* this_block);
static void SplitBlock(block* this_block, size_t need_size) {
    if (align(GetSize(this_block)) - align(need_size) >= 32) {
        block* next_block = GetNextBlock(this_block);
        size_t oldsize = GetSize(this_block);
        this_block->size = (IsFree(this_block) ? align(need_size) | 1 : align(need_size));
        block* new_block = GetNextBlock(this_block);
        new_block->pre_size = this_block->size & (MAX - 1);
        new_block->size = (align(oldsize) - 16 - align(need_size)) | 1;
        if ((void*)next_block < mem_heap_hi())
            next_block->pre_size = new_block->size & (MAX - 1);
        if (this_block == last_block)last_block = new_block;
        //InFreeList(new_block);
        FuseBlock(new_block);
    }
}

static void FuseBlock(block* this_block) {
    //printf("\n\n1\n");
    //printf("\n\nthis_block_data:\nsize:%lu\npre_size:%lu\nnext_block:%p\npre_block:%p\n", this_block->size, this_block->pre_size, this_block->next_block, this_block->pre_block);
    block* pre_block = GetPreBlock(this_block);
    //printf("2\n");
    block* next_block = GetNextBlock(this_block);
    //printf("3\n");
    bool pre_block_free = false, next_block_free = false;
    //printf("pre_block_data:\nsize:%lu\npre_size:%lu\npre_block:%p\nnext_block:%p\n", pre_block->size, pre_block->pre_size, pre_block->pre_block, pre_block->next_block);
    if (this_block->pre_size && pre_block >= limit && IsFree(pre_block)) {
        //printf("\nthis_block pre_size:%lu\n", this_block->pre_size);
        //printf("\n\npre_block >= limit: %d\n", pre_block >= limit);
        //printf("pre_block->pre_block != NULL :%d\n", pre_block->pre_block != NULL);
        //printf("*GetFreeBlockHead(pre_block->size) == pre_block :%d\n", *GetFreeBlockHead(pre_block->size) == pre_block);
        pre_block_free = true;
        //printf("pre_block_data:\nsize:%lu\npre_size:%lu\npre_block:%p\nnext_block:%p\n", pre_block->size, pre_block->pre_size, pre_block->pre_block, pre_block->next_block);
    }
    //printf("4\n");

    if (next_block < (block*)mem_heap_hi() && IsFree(next_block)) {
        next_block_free = true;
        //printf("next_block_data:\nsize:%lu\npre_size:%lu\npre_block:%p\nnext_block:%p\n", next_block->size, next_block->pre_size, next_block->pre_block, next_block->next_block);
    }
    //printf("5\n");
    //printf("pre_block_free:%d   next_block_free:%d\n", pre_block_free, next_block_free);

    if (!pre_block_free && !next_block_free) {
        //printf("\n\nthis_block_data:\nsize:%lu\npre_size:%lu\nnext_block:%p\npre_block:%p\n", this_block->size, this_block->pre_size, this_block->next_block, this_block->pre_block);
        this_block->size = align(GetSize(this_block));
        InFreeList(this_block);
        return;
    }
    else if (pre_block_free && next_block_free) {
        //printf("1\n");
        OutFreeList(pre_block);
        //printf("2\n");
        OutFreeList(next_block);
        //printf("3\n");
        pre_block->size = align(GetSize(this_block)) + align(GetSize(next_block)) + align(GetSize(pre_block)) + 32;
        //printf("4\n");
        if (GetNextBlock(next_block) < (block*)mem_heap_hi())
            GetNextBlock(next_block)->pre_size = pre_block->size & (MAX - 1);
        //printf("\n\nGetNextBlock(next_block)_data\nsize:%lu\npre_size:%lu\nnext_block:%p\npre_block:%p\n", GetNextBlock(next_block)->size, GetNextBlock(next_block)->pre_size, GetNextBlock(next_block)->next_block, GetNextBlock(next_block)->pre_block);
        if (this_block == last_block || next_block == last_block)last_block = pre_block;
        DeleteBlock(this_block);
        DeleteBlock(next_block);
        //printf("head:%p\n", *GetFreeBlockHead(pre_block->size));
        InFreeList(pre_block);
        //printf("5\n");
        return;
    }

    else if (pre_block_free) {
        OutFreeList(pre_block);
        pre_block->size = align(GetSize(this_block)) + align(GetSize(pre_block)) + 16;
        if (next_block < (block*)mem_heap_hi())
            next_block->pre_size = pre_block->size & (MAX - 1);
        if (this_block == last_block)last_block = pre_block;
        DeleteBlock(this_block);
        InFreeList(pre_block);
        return;
    }

    else if (next_block_free) {
        OutFreeList(next_block);
        this_block->size = align(GetSize(next_block)) + align(GetSize(this_block)) + 16;
        if (GetNextBlock(next_block) < (block*)mem_heap_hi())
            GetNextBlock(next_block)->pre_size = this_block->size & (MAX - 1);
        if (next_block == last_block)last_block = this_block;
        DeleteBlock(next_block);
        InFreeList(this_block);
        return;
    }
    return;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    /* IMPLEMENT THIS */
    //printf("%lu\n", sizeof(intptr_t));
    mem_sbrk(32);
    memset(mem_heap_lo(), 0, 32);
    last_block = NULL;
    limit = (block*)((unsigned char*)mem_heap_lo() + 32);
    return true;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    /* IMPLEMENT THIS */
    //printf("malloc begin\n");
    if (mem_heapsize() == 0)mm_init();
    //printf("mem_size:%lu\n", mem_heapsize());
    block** head = GetFreeBlockHead(size);
    if (*head) {
        block* this_block = *head;
        for (; this_block->next_block && GetSize(this_block) < size; this_block = this_block->next_block);
        if (GetSize(this_block) >= size) {
            OutFreeList(this_block);
            SplitBlock(this_block, size);
            //OutFreeList(this_block);
            //printf("malloc end\n");
            return GetPtr(this_block);
        }
    }
    block* new_block = mem_sbrk(0);
    mem_sbrk(align(size) + 16);
    //printf("size:%lu\n", align(size) + 32);
    //if (new_block >= limit && (void*)new_block <= mem_heap_hi());
    //else printf("no\n");
    //if (new_block == (void*)-1)return NULL;
    new_block->size = align(size);
    if (last_block)
        new_block->pre_size = last_block->size & (MAX - 1);
    else
        new_block->pre_size = 0;
    new_block->next_block = new_block->pre_block = NULL;
    last_block = new_block;
    //printf("last_block_size:%lu\n", last_block->pre_size);
    //printf("malloc end\n");
    return GetPtr(new_block);
}

/*
 * free
 */
void free(void* ptr)
{
    /* IMPLEMENT THIS */
    //printf("free begin\n");
    if (!ptr)return;
    //memset(ptr, 0, align(GetHead(ptr)->size));
    //InFreeList(GetHead(ptr));
    FuseBlock(GetHead(ptr));
    //printf("free end\n");
    return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    /* IMPLEMENT THIS */
    //printf("realloc begin\n");
    if (!oldptr)return malloc(size);
    if (!size) {
        free(oldptr);
        return NULL;
    }
    block* this_block = GetHead(oldptr);
    if (this_block->size == size) {
        //printf("realloc end\n");
        return oldptr;
    }
    if (this_block->size > size) {
        SplitBlock(this_block, size);
        //printf("realloc end\n");
        return oldptr;
    }
    //block* next_block = GetNextBlock(this_block);
    /*if (next_block < (block*)mem_heap_hi() && (next_block->pre_block != NULL || *GetFreeBlockHead(next_block->size) == next_block)) {
        if (next_block->size + align(this_block->size) + 32 >= size) {
            OutFreeList(next_block);
            this_block->size = align(this_block->size) + align(next_block->size) + 32;
            block* next_next_block = GetNextBlock(next_block);
            DeleteBlock(next_block);
            SplitBlock(this_block, size);
            if ((void*)next_next_block < mem_heap_hi()) {
                if (GetNextBlock(this_block) == next_next_block)
                    next_next_block->pre_size = this_block->size;
                else next_next_block->pre_size = GetNextBlock(this_block)->size;
            }
            return oldptr;
        }
    }*/
    block* new_block = GetHead(malloc(size));
    memcpy(GetPtr(new_block), oldptr, align(GetSize(GetHead(oldptr))));
    free(oldptr);
    //printf("realloc end\n");
    return GetPtr(new_block);
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t)p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
#endif /* DEBUG */
    if (!mem_heap_lo() % 16) {
        printf("error:line[%d] The header of the heap is not aligned to 16 bytes\n", lineno);
        return false;
    }
    if (last_block){
        if (!IsFree(last_block) && (last_block->next_block != NULL || last_block->pre_block != NULL)) {
            printf("error:line[%d] A not free block is invalid\n", lineno);
            return false;
        }
        if (IsFree(last_block) && (*GetFreeBlockHead(GetSize(last_block)) != last_block && last_block->pre_block == NULL)) {
            printf("error:line[%d] A free block is not in the linked list\n", lineno);
            return false;
        }
    }
    return true;
}
