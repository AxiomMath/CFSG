module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Fischer.Classification.Symplectic

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem zmod_two_add_self (v : M) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod_two_add_add_self (v w : M) : v + (v + w) = w := by
  rw [← add_assoc, zmod_two_add_self, zero_add]

theorem zmod_two_neg (v : M) : -v = v :=
  neg_eq_of_add_eq_zero_left (zmod_two_add_self v)

theorem zmod_two_sub (v w : M) : v - w = v + w := by
  rw [sub_eq_add_neg, zmod_two_neg]

theorem zmod_two_eq_of_add_eq_zero {u v : M} (h : u + v = 0) : u = v := by
  have := congrArg (· + v) h
  simpa [add_assoc, zmod_two_add_self] using this

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem zmod_two_eq_of_add_add (a b c : ZMod 2) (h : a + b + c = 0) : c = b + a := by
  revert a b c
  decide

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 :=
  rfl

theorem zmod_two_eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 :=
  (zmod_two_cases x).resolve_right h

theorem zmod_two_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmod_two_cases x).resolve_left h

macro "zmod_two_abel" : tactic => `(tactic| simp only [add_assoc, add_comm, add_left_comm,
  zmod_two_add_self, zmod_two_add_add_self, add_zero, zero_add])

end CFSG.Fischer.Classification.Symplectic
