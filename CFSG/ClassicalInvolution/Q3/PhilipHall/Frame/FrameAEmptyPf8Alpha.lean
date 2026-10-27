module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_closure_pair_cases {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (hc : t * z = z * t)
    {w : G} (hw : w ∈ Subgroup.closure ({t, z} : Set G)) :
    w = 1 ∨ w = t ∨ w = z ∨ w = t * z := by
  have h1 : z * t * z = t := by
    calc z * t * z = t * z * z := by rw [← hc]
      _ = t := by rw [mul_assoc, hz2, mul_one]
  have h2 : t * (t * z) = z := by rw [← mul_assoc, ht2, one_mul]
  have h3 : z * (t * z) = t := by rw [← mul_assoc, ← hc, mul_assoc, hz2, mul_one]
  have h4 : t * z * t = z := by rw [hc, mul_assoc, ht2, mul_one]
  have h5 : t * z * z = t := by rw [mul_assoc, hz2, mul_one]
  have h6 : (t * z) * (t * z) = 1 := by
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [← hc]
      _ = 1 := by rw [h2, hz2]
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Set.mem_singleton_iff.mp h)))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ht2, hz2, hc.symm, h2, h3, h4, h5, h6]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> subst hx
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ht2))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hz2)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right h6)))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
