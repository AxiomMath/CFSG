module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Polar

variable {V : Type*} [CommGroup V]

structure SympForm (B : V → V → ZMod 2) : Prop where
  sq_eq_one : ∀ a : V, a * a = 1
  mul_left : ∀ a a' b : V, B (a * a') b = B a b + B a' b
  mul_right : ∀ a b b' : V, B a (b * b') = B a b + B a b'
  alt : ∀ a : V, B a a = 0
  nondeg : ∀ a : V, (∀ b : V, B a b = 0) → a = 1

theorem SympForm.symm {B : V → V → ZMod 2} (hB : SympForm B) (a b : V) : B a b = B b a := by
  have h := hB.alt (a * b)
  simp only [hB.mul_left, hB.mul_right, hB.alt, zero_add, add_zero] at h
  revert h
  generalize B a b = x
  generalize B b a = y
  revert x y
  decide

end CFSG.ClassicalInvolution.Q3.Sec13.Polar
