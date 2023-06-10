/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2022                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t S;   /* Operand stack of C0 values */
  ubyte *P;        /* Function body */
  size_t pc;       /* Program counter */
  c0_value *V;     /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool[0].code;      /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  /* Local variables (you won't need this till Task 2) */
  c0_value *V = xmalloc(sizeof(c0_value) * bc0->function_pool[0].num_vars);
  (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  (void) callStack; // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      c0v_push(S, v1);
      c0v_push(S, v2);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      assert(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", val2int(retval)));
      // Free everything before returning from the execute function!
      c0v_stack_free(S);
      free(V);
      if (stack_empty(callStack)){
        stack_free(callStack, NULL);
        return val2int(retval);
      } else {
        frame* f = pop(callStack);
        P = f->P;
        pc = f->pc;
        V = f->V;
        S = f->S;
        free(f);
        c0v_push(S, retval);
      }
      break;
    }


    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      int sum = x + y;
      c0v_push(S, int2val(sum));
      break;
    }

    case ISUB: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      int diff = x - y;
      c0v_push(S, int2val(diff));
      break;
    }

    case IMUL: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      int prod = x * y;
      c0v_push(S, int2val(prod));
      break;
    }

    case IDIV: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (y == 0){
        c0_arith_error("Division by 0");
      }
      else if (x == INT_MIN && y == -1){
        c0_arith_error("Division error");
      }
      else {
        int quo = x / y;
        c0v_push(S, int2val(quo));
      }
      break;
    }

    case IREM: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (y == 0){
        c0_arith_error("Division by 0");
      }
      else if (x == INT_MIN && y == -1){
        c0_arith_error("Division error");
      }
      else {
        int mod = x % y;
        c0v_push(S, int2val(mod));
      }
      break;
    }

    case IAND: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      int and = x & y;
      c0v_push(S, int2val(and));
      break;
    }

    case IOR: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      int or = x | y;
      c0v_push(S, int2val(or));
      break;
    }

    case IXOR: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      int xor = x ^ y;
      c0v_push(S, int2val(xor));
      break;
    }

    case ISHR: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (y >= 32){
        c0_arith_error("Shifting greater than 32 bits error");
      }
      else if (y < 0){
        c0_arith_error("Shifting negative number error");
      }
      else {
        int right_shift = x >> y;
        c0v_push(S, int2val(right_shift));
      }
      break;
    }


    case ISHL: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (y >= 32){
        c0_arith_error("Shifting greater than 32 bits error");
      }
      else if (y < 0){
        c0_arith_error("Shifting negative number error");
      }
      else {
        int right_shift = x << y;
        c0v_push(S, int2val(right_shift));
      }
      break;
    }


    /* Pushing constants */

    case BIPUSH: {
      pc++;
      int32_t c = (int32_t)(int8_t)P[pc];
      c0v_push(S, int2val(c));
      pc++;
      break;
    }

    case ILDC: {
      pc++;
      uint32_t c1 = (uint32_t)P[pc];
      pc++;
      uint32_t c2 = (uint32_t)P[pc];
      pc++;
      int32_t x = bc0->int_pool[c1 << 8| c2];
      c0v_push(S, int2val(x));
      break;
    }

    case ALDC: {
      pc++;
      uint32_t c1 = (uint32_t)P[pc];
      pc++;
      uint32_t c2 = (uint32_t)P[pc];
      pc++;
      char *x = &bc0->string_pool[c1 << 8| c2];
      c0v_push(S, ptr2val((void*)x));
      break;
    }

    case ACONST_NULL: {
      pc++;
      c0v_push(S, ptr2val(NULL));
      break;
    }


    /* Operations on local variables */

    case VLOAD: {
      pc++;
      c0_value v = V[P[pc]];
      c0v_push(S, v);
      pc++;
      break;
    }

    case VSTORE: {
      pc++;
      c0_value v = c0v_pop(S);
      V[P[pc]] = v;
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW: {
      pc++;
      c0_user_error(val2ptr(c0v_pop(S)));
      break;
    }

    case ASSERT: {
      pc++;
      void *ptr = val2ptr(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (x == 0){
        c0_assertion_failure(ptr);
      }
      break;
    }


    /* Control flow operations */

    case NOP: {
      pc++;
      break;
    }

    case IF_CMPEQ: {
      pc++;
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      if (val_equal(v1, v2)) {
        int16_t o1 = (int16_t)(P[pc]);
        pc++;
        int16_t o2 = (int16_t)(P[pc]);
        int16_t to_add = o1 << 8 | o2;
        pc += to_add - 2;
        break;
      } else {
        pc += 2;
      }
      break;
    }

    case IF_CMPNE: {
      pc++;
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      if (!val_equal(v1, v2)) {
        int16_t o1 = (int16_t)(P[pc]);
        pc++;
        int16_t o2 = (int16_t)(P[pc]);
        int16_t to_add = o1 << 8 | o2;
        pc += to_add - 2;
        break;
      } else {
        pc += 2;
      }
      break;
    }

    case IF_ICMPLT: {
      pc++;
      int v1 = val2int(c0v_pop(S));
      int v2 = val2int(c0v_pop(S));
      if (v2 < v1) {
        int16_t o1 = (int16_t)(P[pc]);
        pc++;
        int16_t o2 = (int16_t)(P[pc]);
        int16_t to_add = o1 << 8 | o2;
        pc += to_add - 2;
        break;
      } else {
        pc += 2;
      }
      break;
    }

    case IF_ICMPGE: {
      pc++;
      int v1 = val2int(c0v_pop(S));
      int v2 = val2int(c0v_pop(S));
      if (v2 >= v1) {
        int16_t o1 = (int16_t)(P[pc]);
        pc++;
        int16_t o2 = (int16_t)(P[pc]);
        int16_t to_add = o1 << 8 | o2;
        pc += to_add - 2;
        break;
      } else {
        pc += 2;
      }
      break;
    }

    case IF_ICMPGT: {
      pc++;
      int v1 = val2int(c0v_pop(S));
      int v2 = val2int(c0v_pop(S));
      if (v2 > v1) {
        int16_t o1 = (int16_t)(P[pc]);
        pc++;
        int16_t o2 = (int16_t)(P[pc]);
        int16_t to_add = o1 << 8 | o2;
        pc += to_add - 2;
        break;
      } else {
        pc += 2;
      }
      break;
    }

    case IF_ICMPLE: {
      pc++;
      int v1 = val2int(c0v_pop(S));
      int v2 = val2int(c0v_pop(S));
      if (v2 <= v1) {
        int16_t o1 = (int16_t)(P[pc]);
        pc++;
        int16_t o2 = (int16_t)(P[pc]);
        int16_t to_add = o1 << 8 | o2;
        pc += to_add - 2;        
        break;
      } else {
        pc += 2;
      }
      break;
    }

    case GOTO: {
      pc++;
      int16_t o1 = (int16_t)(P[pc]);
      pc++;
      int16_t o2 = (int16_t)(P[pc]);
      int16_t to_add = o1 << 8 | o2;
      pc += to_add - 2;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      pc++;
      uint16_t c1 = (uint16_t)(P[pc]);
      pc++;
      uint16_t c2 = (uint16_t)(P[pc]);
      uint16_t pos = c1 << 8 | c2;
      pc++;

      struct function_info* g = &bc0->function_pool[pos];

      frame* f = xmalloc(sizeof(frame));
      f->P = P;
      f->pc = pc;
      f->V = V;
      f->S = S;

      push(callStack, (void*)f);
      P = g->code;
      pc = 0;

      V = xmalloc(sizeof(c0_value)*(int)g->num_vars);

      int num_of_args = (int)g->num_args;
      while (num_of_args != 0){
        V[num_of_args - 1] = c0v_pop(S);
        num_of_args -= 1;
      }
      S = c0v_stack_new();
      break;
    }

    case INVOKENATIVE: {
      pc++;
      uint16_t c1 = (uint16_t)(P[pc]);
      pc++;
      uint16_t c2 = (uint16_t)(P[pc]);
      uint16_t pos = c1 << 8 | c2;

      struct native_info* g_native = &bc0->native_pool[pos];

      c0_value* A = xmalloc(sizeof(c0_value)*(int)g_native->num_args);

 
      int num_of_args = (int)g_native->num_args;
      while (num_of_args != 0){
        A[num_of_args - 1] = c0v_pop(S);
        num_of_args -= 1;
      }

      uint16_t index = bc0->native_pool[pos].function_table_index;
      
      c0_value v = (*native_function_table[index])(A);
      c0v_push(S, v);
      pc++;
      break;
    }


    /* Memory allocation and access operations: */

    case NEW: {
      pc++;
      uint8_t size = (uint8_t)P[pc];
      void* new = xmalloc(sizeof(size));
      c0v_push(S, ptr2val(new));
      pc++;
      break;
    }

    case IMLOAD: {
      int* ptr = (int*)val2ptr(c0v_pop(S));
      if (ptr == NULL){
        c0_memory_error("null pointer error");
      }
      int x = *ptr;
      c0v_push(S, int2val(x));
      pc++;
      break;
    }

    case IMSTORE: {
      int x = val2int(c0v_pop(S));
      int* ptr = (int*)val2ptr(c0v_pop(S));
      if (ptr == NULL){
        c0_memory_error("null pointer error");
      }
      *ptr = x;
      pc++;
      break;
    }

    case AMLOAD: {
      void **a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("NULL pointer");
      void *b = *a;
      c0v_push(S, ptr2val(b));
      pc++;
      break;
    }

    case AMSTORE: {
      pc++;
      void *ptr_a = val2ptr(c0v_pop(S));
      void **ptr_b = val2ptr(c0v_pop(S));
      if (ptr_a == NULL || ptr_b == NULL){
        c0_memory_error("null pointer error");
      }
      *ptr_b = ptr_a;
      break;
    }

    case CMLOAD: {
      pc++;
      void *ptr = val2ptr(c0v_pop(S));
      if (ptr == NULL) {
        c0_memory_error("null pointer error");
      } 
      int v = (int)(*((char*)ptr));
      c0v_push(S, int2val(v));
      break;
    }

    case CMSTORE: {
      int v = val2int(c0v_pop(S));
      void* ptr = val2ptr(c0v_pop(S));
      if (ptr == NULL){
        c0_memory_error("null pointer error");
      }
      *((char*)ptr) = v & 0x7f;
      pc++;
      break;   
    }

    case AADDF: {
      pc++;
      void* ptr = val2ptr(c0v_pop(S));
      if (ptr == NULL){
        c0_memory_error("null pointer error");
      }
      ubyte off_set = (ubyte)P[pc];
      void* res = (void*)((char*)ptr + off_set);
      c0v_push(S, ptr2val(res));
      pc++;
      break;
      
    }


    /* Array operations: */

    case NEWARRAY: {
      pc++;
      c0_array* A = xmalloc(sizeof(c0_array));
      int x = val2int(c0v_pop(S));
      if (x < 0){
        c0_memory_error("negative n");
      }
      A->count = x;
      A->elt_size = (int32_t)(int8_t)P[pc];
      A->elems = xcalloc(sizeof(void*), x);
      c0v_push(S, (ptr2val((void*)A)));
      pc++;
      break;
    }

    case ARRAYLENGTH: {
      c0_array* A = (c0_array*)val2ptr(c0v_pop(S));
      if (A == NULL){
        c0_memory_error("null pointer error");
      }
      c0v_push(S, int2val(A->count));
      pc++;
      break;
    }

    case AADDS: {
      int index = val2int(c0v_pop(S));
      void* A = val2ptr(c0v_pop(S));
      if (A == NULL){
        c0_memory_error("null pointer error");
      }
      c0_array* a = (c0_array*)A;
      int count = (int)a->count;
      if (index < 0 || index > count){
        c0_memory_error("index out of bounds error");
      }
      void *res = (((char*)a->elems) + (a->elt_size * index));
      c0v_push(S, ptr2val(res));
      pc++;
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
