module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterResidueCongruence

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse

theorem abelian_character_delta_expansion {G : Type*} [Group G] [IsMulCommutative G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (selected element : G) :
    (∑ label, (basis.representation label).character selected⁻¹ *
      (basis.representation label).character element) = if element = selected then (Nat.card G : ℂ) else 0 := by
  let delta : G → ℂ := fun member => if member = selected then 1 else 0
  have hclass : ∀ member conjugator : G, delta (conjugator * member * conjugator⁻¹) = delta member := by
    intro member conjugator
    have hequal : conjugator * member * conjugator⁻¹ = member := by
      rw [mul_comm' conjugator member, mul_assoc, mul_inv_cancel, mul_one]
    rw [hequal]
  have hcoefficient : ∀ label,
      characterPairing delta (basis.representation label).character =
        (Nat.card G : ℂ)⁻¹ * (basis.representation label).character selected⁻¹ := by
    intro label
    simp only [characterPairing, delta, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hexpansion := finiteIrreducibleCharacterBasis_reconstruction basis delta hclass element
  simp_rw [hcoefficient] at hexpansion
  have hequal := congrArg (fun value : ℂ => (Nat.card G : ℂ) * value) hexpansion
  rw [Finset.mul_sum] at hequal
  simp only [← mul_assoc,
    mul_inv_cancel₀ (show (Nat.card G : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul,
    delta, mul_ite, mul_one, mul_zero] at hequal
  exact hequal.symm

theorem abelian_character_delta_in_algebraic_span {G : Type*} [Group G] [IsMulCommutative G] [Fintype G]
    (selected : G) : (fun element : G => if element = selected then (Nat.card G : ℂ) else 0) ∈
      algebraicCharacterSpan G := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  have hexpansion : (fun element : G => if element = selected then (Nat.card G : ℂ) else 0) =
      ∑ label, algebraicCharacterValue (basis.representation label) selected⁻¹ •
        (basis.representation label).character := by
    funext element
    simp only [Finset.sum_apply, Pi.smul_apply]
    change (if element = selected then (Nat.card G : ℂ) else 0) =
      ∑ label, (basis.representation label).character selected⁻¹ *
        (basis.representation label).character element
    exact (abelian_character_delta_expansion basis selected element).symm
  rw [hexpansion]
  apply Submodule.sum_mem
  intro label _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (character_mem_virtualCharacters _))

theorem algebraicCharacterSpan_inflation {source target : Type groupUniverse} [Group source] [Group target]
    (homomorphism : source →* target) (function : target → ℂ)
    (hmember : function ∈ algebraicCharacterSpan target) :
    function ∘ homomorphism ∈ algebraicCharacterSpan source := by
  induction hmember using Submodule.span_induction with
  | mem character hvirtual => exact Submodule.subset_span (inflation_mem_virtualCharacters homomorphism hvirtual)
  | zero => exact (algebraicCharacterSpan source).zero_mem
  | add left right _ _ hleft hright => exact (algebraicCharacterSpan source).add_mem hleft hright
  | smul scalar function _ hfunction => exact (algebraicCharacterSpan source).smul_mem scalar hfunction

end CFSG.TwoRankLowerBound.Helpers
