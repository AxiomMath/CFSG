module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.EvenSporadicStandard.Fin76b.E613

open AutETable E69

section Group

variable {Γ : Type*} [Group Γ]

theorem closure_pair_subset {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : Γ} (hx : x ∈ Subgroup.closure ({a, b} : Set Γ)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
  have h3 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h5 : a * b * (a * b) = 1 := by rw [mul_assoc, h3, ha]
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, ← hab, true_or, or_true]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · rw [inv_eq_of_mul_eq_one_right ha]; exact Or.inr (Or.inl rfl)
    · rw [inv_eq_of_mul_eq_one_right hb]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [inv_eq_of_mul_eq_one_right h5]; exact Or.inr (Or.inr (Or.inr rfl))

instance innAut_normal : ((MulAut.conj : Γ →* MulAut Γ).range).Normal where
  conj_mem := by
    rintro _ ⟨h, rfl⟩ g
    refine ⟨g h, MulEquiv.ext fun x => ?_⟩
    simp [MulAut.conj_apply]

end Group

end CFSG.EvenSporadicStandard.Fin76b.E613
