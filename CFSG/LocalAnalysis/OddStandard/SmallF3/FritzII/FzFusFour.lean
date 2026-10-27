module

public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G]

theorem fzfus_mem_four {a b g : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) : g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have f1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have f2 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have f3 : b * (a * b) = a := by
    calc b * (a * b) = b * a * b := (mul_assoc _ _ _).symm
      _ = a * b * b := by rw [← hab]
      _ = a := f2
  have f4 : a * b * a = b := by
    calc a * b * a = b * a * a := by rw [hab]
      _ = b := by rw [mul_assoc, ha, mul_one]
  have f5 : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * (a * b)) := mul_assoc _ _ _
      _ = a * a := by rw [f3]
      _ = 1 := ha
  have f6 : b * a = a * b := hab.symm
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have iab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right f5
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp only [mul_one, one_mul, ha, hb, f1, f2, f3, f4, f5, f6, true_or, or_true, eq_self]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;>
      simp only [inv_one, ia, ib, iab, true_or, or_true, eq_self]

end CFSG.OddStandard.SmallF3.FritzII
