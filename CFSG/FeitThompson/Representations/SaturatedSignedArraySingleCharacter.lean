module

import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

section Aux

variable {α : Type*} [Fintype α] {ι : Type*} [Fintype ι]

theorem cfInner_sum_smul_right (f : α → ℂ) (ε : ι → ℂ) (η : ι → α → ℂ) :
    cfInner f (∑ i, ε i • η i) = ∑ i, conj (ε i) * cfInner f (η i) := by
  rw [cfInner_sum_right]
  exact Finset.sum_congr rfl fun i _ => cfInner_smul_right _ _ _

theorem cfInner_sum_smul_left (ε : ι → ℂ) (η : ι → α → ℂ) (f : α → ℂ) :
    cfInner (∑ i, ε i • η i) f = ∑ i, ε i * cfInner (η i) f := by
  rw [cfInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => cfInner_smul_left _ _ _

variable [DecidableEq ι]

theorem IsOrthonormalFamily.cfInner_right_sum_smul {η : ι → α → ℂ} (hη : IsOrthonormalFamily η)
    (ε : ι → ℂ) (i : ι) : cfInner (η i) (∑ j, ε j • η j) = conj (ε i) := by
  rw [cfInner_sum_smul_right, Finset.sum_eq_single i]
  · rw [hη.cfInner_eq_ite i i, if_pos rfl, mul_one]
  · intro j _ hji
    rw [hη.cfInner_eq_ite i j, if_neg (Ne.symm hji), mul_zero]
  · simp

theorem IsOrthonormalFamily.cfInner_left_sum_smul {η : ι → α → ℂ} (hη : IsOrthonormalFamily η)
    (ε : ι → ℂ) (i : ι) : cfInner (∑ j, ε j • η j) (η i) = ε i := by
  rw [cfInner_sum_smul_left, Finset.sum_eq_single i]
  · rw [hη.cfInner_eq_ite i i, if_pos rfl, mul_one]
  · intro j _ hji
    rw [hη.cfInner_eq_ite j i, if_neg hji, mul_zero]
  · simp

theorem IsOrthonormalFamily.cfInner_self_sum_smul {η : ι → α → ℂ} (hη : IsOrthonormalFamily η)
    {ε : ι → ℂ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    cfInner (∑ i, ε i • η i) (∑ i, ε i • η i) = (Fintype.card ι : ℂ) := by
  rw [cfInner_sum_smul_left]
  have h : ∀ i : ι, ε i * cfInner (η i) (∑ j, ε j • η j) = 1 := fun i => by
    rw [hη.cfInner_right_sum_smul]
    rcases hε i with h | h <;> simp [h]
  simp [h]

end Aux

section Main

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]
  {η : ι → G → ℂ} {ε : ι → ℂ} {β χ : G → ℂ}

theorem sum_sign_smul_mem_span_Irr (hηZ : ∀ i, η i ∈ Submodule.span ℤ (Irr G))
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : ∑ i, ε i • η i ∈ Submodule.span ℤ (Irr G) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  rcases hε i with h | h
  · simpa [h] using hηZ i
  · simpa [h] using (Submodule.span ℤ (Irr G)).neg_mem (hηZ i)

variable [Fintype G]

theorem cfInner_self_sum_smul_sub_eq_one [DecidableEq ι] (hη : IsOrthonormalFamily η)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hβ : cfInner β β = (Fintype.card ι : ℂ) + 1)
    (hperp : ∀ i, IsOrthogonal (β - ∑ i, ε i • η i) (η i)) :
    cfInner (∑ i, ε i • η i - β) (∑ i, ε i • η i - β) = 1 := by
  set X : G → ℂ := ∑ i, ε i • η i with hX
  have hXX : cfInner X X = (Fintype.card ι : ℂ) := hη.cfInner_self_sum_smul hε
  have hzero : cfInner (β - X) X = 0 := by
    rw [hX, cfInner_sum_smul_right]
    exact Finset.sum_eq_zero fun i _ => by rw [isOrthogonal_iff.1 (hperp i), mul_zero]
  have h1 : cfInner β X = (Fintype.card ι : ℂ) := by
    have h := cfInner_sub_left β X X
    rw [hzero] at h
    rw [← hXX]; linear_combination -h
  have h2 : cfInner X β = (Fintype.card ι : ℂ) := by rw [← conj_cfInner, h1]; simp
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, h1, h2, hXX, hβ]
  ring

theorem isOrthogonal_sum_smul_sub (hperp : ∀ i, IsOrthogonal (β - ∑ i, ε i • η i) (η i)) (i : ι) :
    IsOrthogonal (∑ i, ε i • η i - β) (η i) := by
  rw [isOrthogonal_iff, show (∑ i, ε i • η i) - β = -(β - ∑ i, ε i • η i) by ring,
    cfInner_neg_left, isOrthogonal_iff.1 (hperp i), neg_zero]

theorem isSignedIrr_sub_of_saturated_signed_array [DecidableEq ι] (hη : IsOrthonormalFamily η)
    (hηZ : ∀ i, η i ∈ Submodule.span ℤ (Irr G)) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hβZ : β ∈ Submodule.span ℤ (Irr G)) (hβ : cfInner β β = (Fintype.card ι : ℂ) + 1)
    (hperp : ∀ i, IsOrthogonal (β - ∑ i, ε i • η i) (η i)) (hχ : χ = ∑ i, ε i • η i - β) :
    χ ∈ signedIrr G ∧ (∀ i, IsOrthogonal χ (η i)) ∧ β = ∑ i, ε i • η i - χ := by
  subst hχ
  refine ⟨mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
      ((Submodule.span ℤ (Irr G)).sub_mem (sum_sign_smul_mem_span_Irr hηZ hε) hβZ)
      (cfInner_self_sum_smul_sub_eq_one hη hε hβ hperp),
    isOrthogonal_sum_smul_sub hperp, (sub_sub_cancel _ _).symm⟩

end Main

theorem isSignedIrr_sub_of_saturated_signed_array_fin {G : Type*} [Group G] [Fintype G] {m n : ℕ}
    {η : Fin m × Fin n → G → ℂ} {ε : Fin m × Fin n → ℂ} {β χ : G → ℂ}
    (hη : IsOrthonormalFamily η) (hηZ : ∀ p, η p ∈ Submodule.span ℤ (Irr G))
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hβZ : β ∈ Submodule.span ℤ (Irr G))
    (hβ : cfInner β β = (m : ℂ) * n + 1)
    (hperp : ∀ p, IsOrthogonal (β - ∑ p, ε p • η p) (η p))
    (hχ : χ = ∑ p, ε p • η p - β) :
    χ ∈ signedIrr G ∧ (∀ p, IsOrthogonal χ (η p)) ∧ β = ∑ p, ε p • η p - χ :=
  isSignedIrr_sub_of_saturated_signed_array hη hηZ hε hβZ
    (by rw [hβ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring) hperp hχ

end CFSG.FeitThompson
