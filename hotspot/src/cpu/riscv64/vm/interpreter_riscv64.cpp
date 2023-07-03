/*
 * Copyright (c) 2013, Red Hat Inc.
 * Copyright (c) 2003, 2011, Oracle and/or its affiliates.
 * All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"
#include "asm/macroAssembler.hpp"
#include "interpreter/bytecodeHistogram.hpp"
#include "interpreter/interpreter.hpp"
#include "interpreter/interpreterGenerator.hpp"
#include "interpreter/interpreterRuntime.hpp"
#include "interpreter/templateTable.hpp"
#include "oops/arrayOop.hpp"
#include "oops/methodData.hpp"
#include "oops/method.hpp"
#include "oops/oop.inline.hpp"
#include "prims/jvmtiExport.hpp"
#include "prims/jvmtiThreadState.hpp"
#include "prims/methodHandles.hpp"
#include "runtime/arguments.hpp"
#include "runtime/deoptimization.hpp"
#include "runtime/frame.inline.hpp"
#include "runtime/sharedRuntime.hpp"
#include "runtime/stubRoutines.hpp"
#include "runtime/synchronizer.hpp"
#include "runtime/timer.hpp"
#include "runtime/vframeArray.hpp"
#include "utilities/debug.hpp"
#ifdef COMPILER1
#include "c1/c1_Runtime1.hpp"
#endif

#define __ _masm->


address AbstractInterpreterGenerator::generate_slow_signature_handler() {
  address entry = __ pc();

  __ andi(esp, esp, -16);
  __ mv(c_rarg3, esp);
  // xmethod
  // xlocals
  // c_rarg3: first stack arg - wordSize
  // adjust sp

  __ addi(sp, c_rarg3, -18 * wordSize);
  __ addi(sp, sp, -2 * wordSize);
  __ sd(lr, Address(sp, 0));

  __ call_VM(noreg,
             CAST_FROM_FN_PTR(address,
                              InterpreterRuntime::slow_signature_handler),
             xmethod, xlocals, c_rarg3);

  // x10: result handler

  // Stack layout:
  // sp: return address           <- sp
  //      1 garbage
  //      8 integer args (if static first is unused)
  //      1 float/double identifiers
  //      8 double args
  //        stack args              <- esp
  //        garbage
  //        expression stack bottom
  //        bcp (NULL)
  //        ...

  // Restore LR
  __ ld(lr, Address(sp, 0));
  __ addi(sp, sp , 2 * wordSize);

  // Do FP first so we can use c_rarg3 as temp
  __ lwu(c_rarg3, Address(sp, 9 * wordSize)); // float/double identifiers

  for (int i = 0; i < Argument::n_float_register_parameters_c; i++) {
    const FloatRegister r = g_FPArgReg[i];
    Label d, done;

    __ andi(t0, c_rarg3, 1UL << i);
    __ bnez(t0, d);
    __ flw(r, Address(sp, (10 + i) * wordSize));
    __ j(done);
    __ bind(d);
    __ fld(r, Address(sp, (10 + i) * wordSize));
    __ bind(done);
  }

  // c_rarg0 contains the result from the call of
  // InterpreterRuntime::slow_signature_handler so we don't touch it
  // here.  It will be loaded with the JNIEnv* later.
  for (int i = 1; i < Argument::n_int_register_parameters_c; i++) {
    const Register rm = g_INTArgReg[i];
    __ ld(rm, Address(sp, i * wordSize));
  }

  __ addi(sp, sp, 18 * wordSize);
  __ ret();

  return entry;
}



//
// Various method entries
//

address InterpreterGenerator::generate_math_entry(AbstractInterpreter::MethodKind kind) {
  // xmethod: Method*
  // x30: sender sp
  // esp: args

  if (!InlineIntrinsics) {
    return NULL; // Generate a vanilla entry
  }

  // These don't need a safepoint check because they aren't virtually
  // callable. We won't enter these intrinsics from compiled code.
  // If in the future we added an intrinsic which was virtually callable
  // we'd have to worry about how to safepoint so that this code is used.

  // mathematical functions inlined by compiler
  // (interpreter must provide identical implementation
  // in order to avoid monotonicity bugs when switching
  // from interpreter to compiler in the middle of some
  // computation)
  //
  // stack:
  //        [ arg ] <-- esp
  //        [ arg ]
  // retaddr in lr

  address fn = NULL;
  address entry_point = NULL;
  Register continuation = lr;
  switch (kind) {
  case Interpreter::java_lang_math_abs:
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ fabs_d(f10, f10);
    __ mv(sp, x30); // Restore caller's SP
    break;
  case Interpreter::java_lang_math_sqrt:
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ fsqrt_d(f10, f10);
    __ mv(sp, x30);
    break;
  case Interpreter::java_lang_math_sin :
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ mv(sp, x30);
    __ mv(x9, lr);
    continuation = x9;  // The first callee-saved register
    if (StubRoutines::dsin() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dsin);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dsin());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  case Interpreter::java_lang_math_cos :
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ mv(sp, x30);
    __ mv(x9, lr);
    continuation = x9;  // The first callee-saved register
    if (StubRoutines::dcos() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dcos);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dcos());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  case Interpreter::java_lang_math_tan :
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ mv(sp, x30);
    __ mv(x9, lr);
    continuation = x9;  // The first callee-saved register
    if (StubRoutines::dtan() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dtan);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dtan());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  case Interpreter::java_lang_math_log :
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ mv(sp, x30);
    __ mv(x9, lr);
    continuation = x9;  // The first callee-saved register
    if (StubRoutines::dlog() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dlog);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dlog());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  case Interpreter::java_lang_math_log10 :
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ mv(sp, x30);
    __ mv(x9, lr);
    continuation = x9;  // The first callee-saved register
    if (StubRoutines::dlog10() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dlog10);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dlog10());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  case Interpreter::java_lang_math_exp :
    entry_point = __ pc();
    __ fld(f10, Address(esp));
    __ mv(sp, x30);
    __ mv(x9, lr);
    continuation = x9;  // The first callee-saved register
    if (StubRoutines::dexp() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dexp);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dexp());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  case Interpreter::java_lang_math_pow :
    entry_point = __ pc();
    __ mv(x9, lr);
    continuation = x9;
    __ fld(f10, Address(esp, 2 * Interpreter::stackElementSize));
    __ fld(f11, Address(esp));
    __ mv(sp, x30);
    if (StubRoutines::dpow() == NULL) {
      fn = CAST_FROM_FN_PTR(address, SharedRuntime::dpow);
    } else {
      fn = CAST_FROM_FN_PTR(address, StubRoutines::dpow());
    }
    __ mv(t0, fn);
    __ jalr(t0);
    break;
  /*case Interpreter::java_lang_math_fmaD :
    if (UseFMA) {
      entry_point = __ pc();
      __ fld(f10, Address(esp, 4 * Interpreter::stackElementSize));
      __ fld(f11, Address(esp, 2 * Interpreter::stackElementSize));
      __ fld(f12, Address(esp));
      __ fmadd_d(f10, f10, f11, f12);
      __ mv(sp, x30); // Restore caller's SP
    }
    break;
  case Interpreter::java_lang_math_fmaF :
    if (UseFMA) {
      entry_point = __ pc();
      __ flw(f10, Address(esp, 2 * Interpreter::stackElementSize));
      __ flw(f11, Address(esp, Interpreter::stackElementSize));
      __ flw(f12, Address(esp));
      __ fmadd_s(f10, f10, f11, f12);
      __ mv(sp, x30); // Restore caller's SP
    }
    break;*/
  default:
    ;
  }
  if (entry_point != NULL) {
    __ jr(continuation);
  }

  return entry_point;
}


  // double trigonometrics and transcendentals
  // static jdouble dsin(jdouble x);
  // static jdouble dcos(jdouble x);
  // static jdouble dtan(jdouble x);
  // static jdouble dlog(jdouble x);
  // static jdouble dlog10(jdouble x);
  // static jdouble dexp(jdouble x);
  // static jdouble dpow(jdouble x, jdouble y);

/*void InterpreterGenerator::generate_transcendental_entry(AbstractInterpreter::MethodKind kind, int fpargs) {
  address fn;
  switch (kind) {
  case Interpreter::java_lang_math_sin :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dsin);
    break;
  case Interpreter::java_lang_math_cos :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dcos);
    break;
  case Interpreter::java_lang_math_tan :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dtan);
    break;
  case Interpreter::java_lang_math_log :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dlog);
    break;
  case Interpreter::java_lang_math_log10 :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dlog10);
    break;
  case Interpreter::java_lang_math_exp :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dexp);
    break;
  case Interpreter::java_lang_math_pow :
    fn = CAST_FROM_FN_PTR(address, SharedRuntime::dpow);
    break;
  default:
    ShouldNotReachHere();
  }
  __ mov(rscratch1, fn);
  __ blr(rscratch1);
}*/

// Abstract method entry
// Attempt to execute abstract method. Throw exception
address InterpreterGenerator::generate_abstract_entry(void) {
  // xmethod: Method*
  // x30: sender SP

  address entry_point = __ pc();

  // abstract method entry

  //  pop return address, reset last_sp to NULL
  __ empty_expression_stack();
  __ restore_bcp();      // bcp must be correct for exception handler   (was destroyed)
  __ restore_locals();   // make sure locals pointer is correct as well (was destroyed)

  // throw exception
  __ call_VM(noreg, CAST_FROM_FN_PTR(address,
                                     InterpreterRuntime::throw_AbstractMethodError),
                                     xmethod);
  // the call_VM checks for exception, so we should never return here.
  __ should_not_reach_here();

  return entry_point;
}


// Empty method, generate a very fast return.
address InterpreterGenerator::generate_empty_entry(void) {
  // rmethod: Method*
  // r13: sender sp must set sp to this value on return

  if (!UseFastEmptyMethods) {
    return NULL;
  }

  address entry_point = __ pc();

  // If we need a safepoint check, generate full interpreter entry.
  Label slow_path;
  {
    int32_t offset=0;
    assert(SafepointSynchronize::_not_synchronized == 0,
           "SafepointSynchronize::_not_synchronized");
    __ la_patchable(t1, SafepointSynchronize::address_of_state(), offset);
    __ lwu(t1, Address(t1, offset));
    __ bnez(t1, slow_path);
  }

  // do nothing for empty methods (do not even increment invocation counter)
  // Code: _return
  // _return
  // return w/o popping parameters
  __ mv(sp, x30); // Restore caller's SP
  __ jr(lr);

  __ bind(slow_path);
  (void) generate_normal_entry(false);
  return entry_point;

}

void Deoptimization::unwind_callee_save_values(frame* f, vframeArray* vframe_array) {

  // This code is sort of the equivalent of C2IAdapter::setup_stack_frame back in
  // the days we had adapter frames. When we deoptimize a situation where a
  // compiled caller calls a compiled caller will have registers it expects
  // to survive the call to the callee. If we deoptimize the callee the only
  // way we can restore these registers is to have the oldest interpreter
  // frame that we create restore these values. That is what this routine
  // will accomplish.

  // At the moment we have modified c2 to not have any callee save registers
  // so this problem does not exist and this routine is just a place holder.

  assert(f->is_interpreted_frame(), "must be interpreted");
}
