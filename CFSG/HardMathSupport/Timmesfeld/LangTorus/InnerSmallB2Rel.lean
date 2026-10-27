module

public import CFSG.CGT.PushingUpLit.BHSSym.Coxeter
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym Equiv Equiv.Perm

section B2

variable {H : Type*} [Group H]

structure B2Rel (s ms l ml a ma b mb : H) : Prop where
  r0 : s * s = 1
  r1 : ms * ms = 1
  r2 : l * l = 1
  r3 : ml * ml = 1
  r4 : a * a = 1
  r5 : ma * ma = 1
  r6 : b * b = 1
  r7 : mb * mb = 1
  r8 : ms * s * ms = s * ms * s
  r9 : ms * l = l * ms
  r10 : ms * a = a * ms
  r11 : ms * b * ms * b = a * l
  r12 : s * l * s * l = a * b
  r13 : ml * s = s * ml
  r14 : ms * ml * ms * ml = ma * mb
  r15 : ml * l * ml = l * ml * l
  r16 : a * ml * a * ml = s * b
  r17 : ml * b = b * ml
  r18 : a * s = s * a
  r19 : a * l = l * a
  r20 : a * b = b * a
  r21 : ma * s = s * ma
  r22 : ma * ms = ms * ma
  r23 : ma * l * ma * l = ms * mb
  r24 : ma * ml = ml * ma
  r25 : ma * a * ma = a * ma * a
  r26 : ma * b * ma * b = s * ml
  r27 : ma * mb = mb * ma
  r28 : b * s = s * b
  r29 : b * l = l * b
  r30 : s * mb * s * mb = ma * ml
  r31 : mb * ms = ms * mb
  r32 : mb * l = l * mb
  r33 : mb * ml = ml * mb
  r34 : a * mb * a * mb = ms * l
  r35 : mb * b * mb = b * mb * b

variable {s ms l ml a ma b mb : H}

theorem step_word (p q lhs rhs : List H) (hr : ∀ w : H, lhs.prod * w = rhs.prod * w) :
    (p ++ lhs ++ q).prod = (p ++ rhs ++ q).prod := by
  simp only [List.append_assoc, List.prod_append]
  exact congrArg (p.prod * ·) (hr q.prod)

theorem B2Rel.r0' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([s, s] : List H).prod * w = ([] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r0

theorem B2Rel.r1' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ms, ms] : List H).prod * w = ([] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r1

theorem B2Rel.r2' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([l, l] : List H).prod * w = ([] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r2

theorem B2Rel.r3' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ml, ml] : List H).prod * w = ([] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r3

theorem B2Rel.r5' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ma, ma] : List H).prod * w = ([] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r5

theorem B2Rel.r7' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([mb, mb] : List H).prod * w = ([] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r7

theorem B2Rel.r11' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ms, b, ms, b] : List H).prod * w = ([a, l] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r11

theorem B2Rel.r13' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ml, s] : List H).prod * w = ([s, ml] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r13

theorem B2Rel.r14' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ms, ml, ms, ml] : List H).prod * w = ([ma, mb] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r14

theorem B2Rel.r15' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ml, l, ml] : List H).prod * w = ([l, ml, l] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r15

theorem B2Rel.r17' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ml, b] : List H).prod * w = ([b, ml] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r17

theorem B2Rel.r21' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ma, s] : List H).prod * w = ([s, ma] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r21

theorem B2Rel.r23' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ma, l, ma, l] : List H).prod * w = ([ms, mb] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r23

theorem B2Rel.r24' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ma, ml] : List H).prod * w = ([ml, ma] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r24

theorem B2Rel.r26' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ma, b, ma, b] : List H).prod * w = ([s, ml] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r26

theorem B2Rel.r27' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([ma, mb] : List H).prod * w = ([mb, ma] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r27

theorem B2Rel.r28' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([b, s] : List H).prod * w = ([s, b] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r28

theorem B2Rel.r29' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([b, l] : List H).prod * w = ([l, b] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r29

theorem B2Rel.r30' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([s, mb, s, mb] : List H).prod * w = ([ma, ml] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r30

theorem B2Rel.r32' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([mb, l] : List H).prod * w = ([l, mb] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r32

theorem B2Rel.r33' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([mb, ml] : List H).prod * w = ([ml, mb] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r33

theorem B2Rel.r35' (h : B2Rel s ms l ml a ma b mb) (w : H) :
    ([mb, b, mb] : List H).prod * w = ([b, mb, b] : List H).prod * w := by
  simpa [mul_assoc] using congrArg (· * w) h.r35
theorem b2_sqT (h : B2Rel s ms l ml a ma b mb) :
    s * mb * s * s * mb * s = 1 := by
  have key : ([s, mb, s, s, mb, s] : List H).prod = ([] : List H).prod := by
    calc ([s, mb, s, s, mb, s] : List H).prod
      _ = ([ml, ml, s, mb, s, s, mb, s] : List H).prod := step_word [] [s, mb, s, s, mb, s] [] [ml, ml] (fun w => (B2Rel.r3' h w).symm)
      _ = ([ml, s, ml, mb, s, s, mb, s] : List H).prod := step_word [ml] [mb, s, s, mb, s] [ml, s] [s, ml] (B2Rel.r13' h)
      _ = ([ml, s, ml, mb, mb, s] : List H).prod := step_word [ml, s, ml, mb] [mb, s] [s, s] [] (B2Rel.r0' h)
      _ = ([ml, s, ml, s] : List H).prod := step_word [ml, s, ml] [s] [mb, mb] [] (B2Rel.r7' h)
      _ = ([s, ml, ml, s] : List H).prod := step_word [] [ml, s] [ml, s] [s, ml] (B2Rel.r13' h)
      _ = ([s, s] : List H).prod := step_word [s] [s] [ml, ml] [] (B2Rel.r3' h)
      _ = ([] : List H).prod := step_word [] [] [s, s] [] (B2Rel.r0' h)
  simpa [mul_assoc] using key

theorem b2_braid01 (h : B2Rel s ms l ml a ma b mb) :
    mb * b * mb = b * mb * b := by
  have key : ([mb, b, mb] : List H).prod = ([b, mb, b] : List H).prod := by
    calc ([mb, b, mb] : List H).prod
      _ = ([b, mb, b] : List H).prod := step_word [] [] [mb, b, mb] [b, mb, b] (B2Rel.r35' h)
  simpa [mul_assoc] using key

theorem b2_braid12 (h : B2Rel s ms l ml a ma b mb) :
    b * s * mb * s * b = s * mb * s * b * s * mb * s := by
  have key : ([b, s, mb, s, b] : List H).prod = ([s, mb, s, b, s, mb, s] : List H).prod := by
    calc ([b, s, mb, s, b] : List H).prod
      _ = ([s, b, mb, s, b] : List H).prod := step_word [] [mb, s, b] [b, s] [s, b] (B2Rel.r28' h)
      _ = ([s, b, mb, b, s] : List H).prod := step_word [s, b, mb] [] [s, b] [b, s] (fun w => (B2Rel.r28' h w).symm)
      _ = ([s, mb, b, mb, s] : List H).prod := step_word [s] [s] [b, mb, b] [mb, b, mb] (fun w => (B2Rel.r35' h w).symm)
      _ = ([s, mb, s, s, b, mb, s] : List H).prod := step_word [s, mb] [b, mb, s] [] [s, s] (fun w => (B2Rel.r0' h w).symm)
      _ = ([s, mb, s, b, s, mb, s] : List H).prod := step_word [s, mb, s] [mb, s] [s, b] [b, s] (fun w => (B2Rel.r28' h w).symm)
  simpa [mul_assoc] using key

theorem b2_braid23 (h : B2Rel s ms l ml a ma b mb) :
    s * mb * s * l * s * mb * s = l * s * mb * s * l := by
  have key : ([s, mb, s, l, s, mb, s] : List H).prod = ([l, s, mb, s, l] : List H).prod := by
    calc ([s, mb, s, l, s, mb, s] : List H).prod
      _ = ([s, mb, s, mb, mb, l, s, mb, s] : List H).prod := step_word [s, mb, s] [l, s, mb, s] [] [mb, mb] (fun w => (B2Rel.r7' h w).symm)
      _ = ([ma, ml, mb, l, s, mb, s] : List H).prod := step_word [] [mb, l, s, mb, s] [s, mb, s, mb] [ma, ml] (B2Rel.r30' h)
      _ = ([ma, ml, mb, l, s, mb, s, mb, mb] : List H).prod := step_word [ma, ml, mb, l, s, mb, s] [] [] [mb, mb] (fun w => (B2Rel.r7' h w).symm)
      _ = ([ma, ml, mb, l, ma, ml, mb] : List H).prod := step_word [ma, ml, mb, l] [mb] [s, mb, s, mb] [ma, ml] (B2Rel.r30' h)
      _ = ([mb, mb, ma, ml, mb, l, ma, ml, mb] : List H).prod := step_word [] [ma, ml, mb, l, ma, ml, mb] [] [mb, mb] (fun w => (B2Rel.r7' h w).symm)
      _ = ([mb, ma, mb, ml, mb, l, ma, ml, mb] : List H).prod := step_word [mb] [ml, mb, l, ma, ml, mb] [mb, ma] [ma, mb] (fun w => (B2Rel.r27' h w).symm)
      _ = ([mb, ms, ml, ms, ml, ml, mb, l, ma, ml, mb] : List H).prod := step_word [mb] [ml, mb, l, ma, ml, mb] [ma, mb] [ms, ml, ms, ml] (fun w => (B2Rel.r14' h w).symm)
      _ = ([mb, ms, ml, ms, mb, l, ma, ml, mb] : List H).prod := step_word [mb, ms, ml, ms] [mb, l, ma, ml, mb] [ml, ml] [] (B2Rel.r3' h)
      _ = ([mb, ms, ml, ma, l, ma, l, l, ma, ml, mb] : List H).prod := step_word [mb, ms, ml] [l, ma, ml, mb] [ms, mb] [ma, l, ma, l] (fun w => (B2Rel.r23' h w).symm)
      _ = ([mb, ms, ml, ma, l, ma, ma, ml, mb] : List H).prod := step_word [mb, ms, ml, ma, l, ma] [ma, ml, mb] [l, l] [] (B2Rel.r2' h)
      _ = ([mb, ms, ml, ma, l, ml, mb] : List H).prod := step_word [mb, ms, ml, ma, l] [ml, mb] [ma, ma] [] (B2Rel.r5' h)
      _ = ([mb, ms, ma, ml, l, ml, mb] : List H).prod := step_word [mb, ms] [l, ml, mb] [ml, ma] [ma, ml] (fun w => (B2Rel.r24' h w).symm)
      _ = ([mb, ms, ma, l, ml, l, mb] : List H).prod := step_word [mb, ms, ma] [mb] [ml, l, ml] [l, ml, l] (B2Rel.r15' h)
      _ = ([mb, ms, ma, l, ml, mb, l] : List H).prod := step_word [mb, ms, ma, l, ml] [] [l, mb] [mb, l] (fun w => (B2Rel.r32' h w).symm)
      _ = ([mb, ms, ma, l, ma, ma, ml, mb, l] : List H).prod := step_word [mb, ms, ma, l] [ml, mb, l] [] [ma, ma] (fun w => (B2Rel.r5' h w).symm)
      _ = ([mb, ms, ma, l, ma, l, l, ma, ml, mb, l] : List H).prod := step_word [mb, ms, ma, l, ma] [ma, ml, mb, l] [] [l, l] (fun w => (B2Rel.r2' h w).symm)
      _ = ([mb, ms, ms, mb, l, ma, ml, mb, l] : List H).prod := step_word [mb, ms] [l, ma, ml, mb, l] [ma, l, ma, l] [ms, mb] (B2Rel.r23' h)
      _ = ([mb, mb, l, ma, ml, mb, l] : List H).prod := step_word [mb] [mb, l, ma, ml, mb, l] [ms, ms] [] (B2Rel.r1' h)
      _ = ([l, ma, ml, mb, l] : List H).prod := step_word [] [l, ma, ml, mb, l] [mb, mb] [] (B2Rel.r7' h)
      _ = ([l, s, mb, s, mb, mb, l] : List H).prod := step_word [l] [mb, l] [ma, ml] [s, mb, s, mb] (fun w => (B2Rel.r30' h w).symm)
      _ = ([l, s, mb, s, l] : List H).prod := step_word [l, s, mb, s] [l] [mb, mb] [] (B2Rel.r7' h)
  simpa [mul_assoc] using key

theorem b2_braid34 (h : B2Rel s ms l ml a ma b mb) :
    l * ml * l = ml * l * ml := by
  have key : ([l, ml, l] : List H).prod = ([ml, l, ml] : List H).prod := by
    calc ([l, ml, l] : List H).prod
      _ = ([ml, l, ml] : List H).prod := step_word [] [] [l, ml, l] [ml, l, ml] (fun w => (B2Rel.r15' h w).symm)
  simpa [mul_assoc] using key

theorem b2_c02 (h : B2Rel s ms l ml a ma b mb) :
    mb * s * mb * s = s * mb * s * mb := by
  have key : ([mb, s, mb, s] : List H).prod = ([s, mb, s, mb] : List H).prod := by
    calc ([mb, s, mb, s] : List H).prod
      _ = ([ml, ml, mb, s, mb, s] : List H).prod := step_word [] [mb, s, mb, s] [] [ml, ml] (fun w => (B2Rel.r3' h w).symm)
      _ = ([ml, ma, ma, ml, mb, s, mb, s] : List H).prod := step_word [ml] [ml, mb, s, mb, s] [] [ma, ma] (fun w => (B2Rel.r5' h w).symm)
      _ = ([ml, ma, s, mb, s, mb, mb, s, mb, s] : List H).prod := step_word [ml, ma] [mb, s, mb, s] [ma, ml] [s, mb, s, mb] (fun w => (B2Rel.r30' h w).symm)
      _ = ([ml, ma, s, mb, s, s, mb, s] : List H).prod := step_word [ml, ma, s, mb, s] [s, mb, s] [mb, mb] [] (B2Rel.r7' h)
      _ = ([ml, ma, s, mb, mb, s] : List H).prod := step_word [ml, ma, s, mb] [mb, s] [s, s] [] (B2Rel.r0' h)
      _ = ([ml, ma, s, s] : List H).prod := step_word [ml, ma, s] [s] [mb, mb] [] (B2Rel.r7' h)
      _ = ([ml, ma] : List H).prod := step_word [ml, ma] [] [s, s] [] (B2Rel.r0' h)
      _ = ([ma, ml] : List H).prod := step_word [] [] [ml, ma] [ma, ml] (fun w => (B2Rel.r24' h w).symm)
      _ = ([s, mb, s, mb] : List H).prod := step_word [] [] [ma, ml] [s, mb, s, mb] (fun w => (B2Rel.r30' h w).symm)
  simpa [mul_assoc] using key

theorem b2_c03 (h : B2Rel s ms l ml a ma b mb) :
    mb * l = l * mb := by
  have key : ([mb, l] : List H).prod = ([l, mb] : List H).prod := by
    calc ([mb, l] : List H).prod
      _ = ([l, mb] : List H).prod := step_word [] [] [mb, l] [l, mb] (B2Rel.r32' h)
  simpa [mul_assoc] using key

theorem b2_c04 (h : B2Rel s ms l ml a ma b mb) :
    mb * ml = ml * mb := by
  have key : ([mb, ml] : List H).prod = ([ml, mb] : List H).prod := by
    calc ([mb, ml] : List H).prod
      _ = ([ml, mb] : List H).prod := step_word [] [] [mb, ml] [ml, mb] (B2Rel.r33' h)
  simpa [mul_assoc] using key

theorem b2_c13 (h : B2Rel s ms l ml a ma b mb) :
    b * l = l * b := by
  have key : ([b, l] : List H).prod = ([l, b] : List H).prod := by
    calc ([b, l] : List H).prod
      _ = ([l, b] : List H).prod := step_word [] [] [b, l] [l, b] (B2Rel.r29' h)
  simpa [mul_assoc] using key

theorem b2_c14 (h : B2Rel s ms l ml a ma b mb) :
    b * ml = ml * b := by
  have key : ([b, ml] : List H).prod = ([ml, b] : List H).prod := by
    calc ([b, ml] : List H).prod
      _ = ([ml, b] : List H).prod := step_word [] [] [b, ml] [ml, b] (fun w => (B2Rel.r17' h w).symm)
  simpa [mul_assoc] using key

theorem b2_c24 (h : B2Rel s ms l ml a ma b mb) :
    s * mb * s * ml = ml * s * mb * s := by
  have key : ([s, mb, s, ml] : List H).prod = ([ml, s, mb, s] : List H).prod := by
    calc ([s, mb, s, ml] : List H).prod
      _ = ([s, mb, ml, s] : List H).prod := step_word [s, mb] [] [s, ml] [ml, s] (fun w => (B2Rel.r13' h w).symm)
      _ = ([s, ml, mb, s] : List H).prod := step_word [s] [s] [mb, ml] [ml, mb] (B2Rel.r33' h)
      _ = ([ml, s, mb, s] : List H).prod := step_word [] [mb, s] [s, ml] [ml, s] (fun w => (B2Rel.r13' h w).symm)
  simpa [mul_assoc] using key

theorem b2_ma (h : B2Rel s ms l ml a ma b mb) :
    ma = mb * s * mb * s * ml := by
  have key : ([ma] : List H).prod = ([mb, s, mb, s, ml] : List H).prod := by
    calc ([ma] : List H).prod
      _ = ([s, s, ma] : List H).prod := step_word [] [ma] [] [s, s] (fun w => (B2Rel.r0' h w).symm)
      _ = ([s, ma, s] : List H).prod := step_word [s] [] [s, ma] [ma, s] (fun w => (B2Rel.r21' h w).symm)
      _ = ([s, ma, s, ml, ml] : List H).prod := step_word [s, ma, s] [] [] [ml, ml] (fun w => (B2Rel.r3' h w).symm)
      _ = ([s, ma, ml, s, ml] : List H).prod := step_word [s, ma] [ml] [s, ml] [ml, s] (fun w => (B2Rel.r13' h w).symm)
      _ = ([s, s, mb, s, mb, s, ml] : List H).prod := step_word [s] [s, ml] [ma, ml] [s, mb, s, mb] (fun w => (B2Rel.r30' h w).symm)
      _ = ([mb, s, mb, s, ml] : List H).prod := step_word [] [mb, s, mb, s, ml] [s, s] [] (B2Rel.r0' h)
  simpa [mul_assoc] using key

theorem b2_s (h : B2Rel s ms l ml a ma b mb) :
    s = ma * b * ma * b * ml := by
  have key : ([s] : List H).prod = ([ma, b, ma, b, ml] : List H).prod := by
    calc ([s] : List H).prod
      _ = ([s, ml, ml] : List H).prod := step_word [s] [] [] [ml, ml] (fun w => (B2Rel.r3' h w).symm)
      _ = ([ma, b, ma, b, ml] : List H).prod := step_word [] [ml] [s, ml] [ma, b, ma, b] (fun w => (B2Rel.r26' h w).symm)
  simpa [mul_assoc] using key

theorem b2_ms (h : B2Rel s ms l ml a ma b mb) :
    ms = ma * l * ma * l * mb := by
  have key : ([ms] : List H).prod = ([ma, l, ma, l, mb] : List H).prod := by
    calc ([ms] : List H).prod
      _ = ([ms, mb, mb] : List H).prod := step_word [ms] [] [] [mb, mb] (fun w => (B2Rel.r7' h w).symm)
      _ = ([ma, l, ma, l, mb] : List H).prod := step_word [] [mb] [ms, mb] [ma, l, ma, l] (fun w => (B2Rel.r23' h w).symm)
  simpa [mul_assoc] using key

theorem b2_a (h : B2Rel s ms l ml a ma b mb) :
    a = ms * b * ms * b * l := by
  have key : ([a] : List H).prod = ([ms, b, ms, b, l] : List H).prod := by
    calc ([a] : List H).prod
      _ = ([a, l, l] : List H).prod := step_word [a] [] [] [l, l] (fun w => (B2Rel.r2' h w).symm)
      _ = ([ms, b, ms, b, l] : List H).prod := step_word [] [l] [a, l] [ms, b, ms, b] (fun w => (B2Rel.r11' h w).symm)
  simpa [mul_assoc] using key

@[expose] def b2t (s ms l ml a ma b mb : H) : ℕ → H
  | 0 => mb
  | 1 => b
  | 2 => s * mb * s
  | 3 => l
  | 4 => ml
  | _ => 1

theorem b2_isCoxeterA (h : B2Rel s ms l ml a ma b mb) :
    IsCoxeterA 5 (b2t s ms l ml a ma b mb) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
  · interval_cases i
    · exact h.r7
    · exact h.r6
    · simpa [b2t, mul_assoc] using b2_sqT h
    · exact h.r2
    · exact h.r3
  · have hi4 : i < 4 := by omega
    interval_cases i
    · simpa [b2t, mul_assoc] using b2_braid01 h
    · simpa [b2t, mul_assoc] using b2_braid12 h
    · simpa [b2t, mul_assoc] using b2_braid23 h
    · simpa [b2t, mul_assoc] using b2_braid34 h
  · have hc : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 3) ∨
        (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by omega
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [b2t, mul_assoc] using b2_c02 h
    · simpa [b2t, mul_assoc] using b2_c03 h
    · simpa [b2t, mul_assoc] using b2_c04 h
    · simpa [b2t, mul_assoc] using b2_c13 h
    · simpa [b2t, mul_assoc] using b2_c14 h
    · simpa [b2t, mul_assoc] using b2_c24 h

theorem b2_closure_eq (h : B2Rel s ms l ml a ma b mb) :
    Subgroup.closure ({s, ms, l, ml, a, ma, b, mb} : Set H) =
      Subgroup.closure (b2t s ms l ml a ma b mb '' Set.Iio 5) := by
  set E := Subgroup.closure (b2t s ms l ml a ma b mb '' Set.Iio 5) with hE
  have hmb : mb ∈ E := Subgroup.subset_closure ⟨0, by simp, rfl⟩
  have hb : b ∈ E := Subgroup.subset_closure ⟨1, by simp, rfl⟩
  have hT : s * mb * s ∈ E := Subgroup.subset_closure ⟨2, by simp, rfl⟩
  have hl : l ∈ E := Subgroup.subset_closure ⟨3, by simp, rfl⟩
  have hml : ml ∈ E := Subgroup.subset_closure ⟨4, by simp, rfl⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    have hma : ma ∈ E := by
      have e : ma = mb * (s * mb * s) * ml := by simpa [mul_assoc] using b2_ma h
      rw [e]
      exact mul_mem (mul_mem hmb hT) hml
    have hs : s ∈ E := by
      rw [b2_s h]
      exact mul_mem (mul_mem (mul_mem (mul_mem hma hb) hma) hb) hml
    have hms : ms ∈ E := by
      rw [b2_ms h]
      exact mul_mem (mul_mem (mul_mem (mul_mem hma hl) hma) hl) hmb
    have ha : a ∈ E := by
      rw [b2_a h]
      exact mul_mem (mul_mem (mul_mem (mul_mem hms hb) hms) hb) hl
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 5 := hi
    have hmem : ∀ x ∈ ({s, ms, l, ml, a, ma, b, mb} : Set H),
        x ∈ Subgroup.closure ({s, ms, l, ml, a, ma, b, mb} : Set H) := fun x hx =>
      Subgroup.subset_closure hx
    have hs : s ∈ Subgroup.closure ({s, ms, l, ml, a, ma, b, mb} : Set H) := hmem s (by simp)
    have hmb' : mb ∈ Subgroup.closure ({s, ms, l, ml, a, ma, b, mb} : Set H) := hmem mb (by simp)
    interval_cases i
    · exact hmb'
    · exact hmem b (by simp)
    · exact mul_mem (mul_mem hs hmb') hs
    · exact hmem l (by simp)
    · exact hmem ml (by simp)

theorem t_ne_two {t : ℕ → H} (hx : IsCoxeterA 5 t) (h01 : t 0 ≠ t 1) : t 0 ≠ t 2 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 5 t hx
  intro h02
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hsw0 : adjSwap 5 0 = swap (0 : Fin 6) 1 := adjSwap_of_lt (by norm_num)
  have hsw1 : adjSwap 5 1 = swap (1 : Fin 6) 2 := adjSwap_of_lt (by norm_num)
  have hsw2 : adjSwap 5 2 = swap (2 : Fin 6) 3 := adjSwap_of_lt (by norm_num)
  have hσA : adjSwap 5 0 * adjSwap 5 2 ∈ alternatingGroup (Fin 6) := by
    rw [mem_alternatingGroup, hsw0, hsw2, map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  have hcA : adjSwap 5 0 * adjSwap 5 1 ∈ alternatingGroup (Fin 6) := by
    rw [mem_alternatingGroup, hsw0, hsw1, map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide
  have hσk : ψ (adjSwap 5 0 * adjSwap 5 2) = 1 := by
    rw [map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num), ← h02, hx.sq 0 (by norm_num)]
  have hσne : (⟨adjSwap 5 0 * adjSwap 5 2, hσA⟩ : alternatingGroup (Fin 6)) ≠ 1 := by
    intro h
    have := congrArg (fun x : alternatingGroup (Fin 6) => (x : Perm (Fin 6)) (0 : Fin 6)) h
    simp [hsw0, hsw2] at this
    revert this
    decide
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (ψ.ker.subgroupOf (alternatingGroup (Fin 6))) with hbot | htop
  · apply hσne
    have : (⟨adjSwap 5 0 * adjSwap 5 2, hσA⟩ : alternatingGroup (Fin 6)) ∈
        ψ.ker.subgroupOf (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hσk
    rw [hbot] at this
    exact this
  · have hc : (⟨adjSwap 5 0 * adjSwap 5 1, hcA⟩ : alternatingGroup (Fin 6)) ∈
        ψ.ker.subgroupOf (alternatingGroup (Fin 6)) := by rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf] at hc
    have hc' : ψ (adjSwap 5 0 * adjSwap 5 1) = 1 := hc
    rw [map_mul, hψ 0 (by norm_num), hψ 1 (by norm_num)] at hc'
    apply h01
    calc t 0 = t 0 * (t 1 * t 1) := by rw [hx.sq 1 (by norm_num), mul_one]
      _ = (t 0 * t 1) * t 1 := by rw [mul_assoc]
      _ = t 1 := by rw [hc', one_mul]

theorem exists_mulEquiv_closure_five {t : ℕ → H} (hx : IsCoxeterA 5 t) (h01 : t 0 ≠ t 1) :
    ∃ e : Perm (Fin 6) ≃* ↥(Subgroup.closure (t '' Set.Iio 5)),
      ∀ i, i < 5 → ((e (adjSwap 5 i) : ↥(Subgroup.closure (t '' Set.Iio 5))) : H) = t i :=
  exists_mulEquiv_closure (by norm_num) hx h01 (fun _ => t_ne_two hx h01)

end B2

end CFSG.HardMathSupport.Timmesfeld.LangTorus
