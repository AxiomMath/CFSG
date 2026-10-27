module

public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.CharacterTheory.OddOrderBasics.Schur

public section

open scoped BigOperators Classical

namespace CFSG.CentralInvolution

open TwoRankLowerBound.Helpers BlockSectionOrthogonality.Helpers CFSG.DirectProduct

@[expose] noncomputable def centralInvolutionSign {H : Type*} (t : H) [One H] (χ : H → ℂ) : ℂ :=
  χ t / χ 1

theorem exists_sign_mul_central_involution {H : Type} [Group H] [Fintype H] {t : H}
    (ht : t ∈ Subgroup.center H) (ht2 : t ^ 2 = 1) {χ : H → ℂ} (hχ : χ ∈ BlocksIrr H) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧ ∀ h, χ (h * t) = c * χ h := by
  have hdeg := identity_ne_zero_of_mem hχ
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  have hT : ∀ g : H, ρ t ∘ₗ ρ g = ρ g ∘ₗ ρ t := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp ht g]
  obtain ⟨c, hc⟩ := CFSG.OddOrderBasics.complex_irreducible_commuting_scalar ρ hirr (ρ t) hT
  have hval : ∀ h, ρ.character (h * t) = c * ρ.character h := by
    intro h
    have h1 : ρ (h * t) = c • ρ h := by
      rw [map_mul, hc, Module.End.mul_eq_comp, LinearMap.comp_smul, LinearMap.comp_id]
    simp only [Representation.character, h1, map_smul, smul_eq_mul]
  refine ⟨c, ?_, hval⟩
  have h1 : ρ.character 1 = c * (c * ρ.character 1) := by
    have h2 := hval t
    have h3 := hval 1
    rw [one_mul] at h3
    rw [h3, ← sq, ht2] at h2
    exact h2
  have h3 : c * c = 1 := by
    have h4 : (c * c - 1) * ρ.character 1 = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linear_combination h5
    · exact absurd h5 hdeg
  exact mul_self_eq_one_iff.mp h3

theorem central_involution_character_parity {H : Type} [Group H] [Fintype H] (t : H)
    (ht : t ∈ Subgroup.center H) (ht2 : orderOf t = 2) :
    (∀ χ ∈ BlocksIrr H,
      (centralInvolutionSign t χ = 1 ∨ centralInvolutionSign t χ = -1) ∧
        (∀ h, χ (h * t) = centralInvolutionSign t χ * χ h) ∧
        ∀ ε : ℂ, (∀ h, χ (h * t) = ε * χ h) → ε = centralInvolutionSign t χ) ∧
    ∀ (c : (H → ℂ) → ℂ) (ε : ℂ), (ε = 1 ∨ ε = -1) →
      ((∀ h, (∑ χ ∈ (irreducibles_finite H).toFinset, c χ • χ) (h * t) =
          ε * (∑ χ ∈ (irreducibles_finite H).toFinset, c χ • χ) h) ↔
        ∀ χ ∈ BlocksIrr H, centralInvolutionSign t χ ≠ ε → c χ = 0) := by
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hsign : ∀ χ ∈ BlocksIrr H,
      (centralInvolutionSign t χ = 1 ∨ centralInvolutionSign t χ = -1) ∧
        (∀ h, χ (h * t) = centralInvolutionSign t χ * χ h) ∧
        ∀ ε : ℂ, (∀ h, χ (h * t) = ε * χ h) → ε = centralInvolutionSign t χ := by
    intro χ hχ
    have hdeg := identity_ne_zero_of_mem hχ
    have huniq : ∀ ε : ℂ, (∀ h, χ (h * t) = ε * χ h) → ε = centralInvolutionSign t χ := by
      intro ε hε
      have h1 := hε 1
      rw [one_mul] at h1
      rw [centralInvolutionSign, h1, mul_div_cancel_right₀ _ hdeg]
    obtain ⟨c, hc, hval⟩ := exists_sign_mul_central_involution ht ht2' hχ
    have hcs := huniq c hval
    rw [← hcs]
    exact ⟨hc, hval, fun ε hε => (huniq ε hε).trans hcs.symm⟩
  refine ⟨hsign, fun c ε hε => ?_⟩
  have hshift : ∀ h, (∑ χ ∈ (irreducibles_finite H).toFinset, c χ • χ) (h * t) =
      ∑ χ ∈ (irreducibles_finite H).toFinset, (c χ * centralInvolutionSign t χ) • χ h := by
    intro h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [(hsign χ ((Set.Finite.mem_toFinset _).mp hχ)).2.1 h]
    ring
  constructor
  · intro hpar χ hχ hne
    have hzero : (∑ ψ ∈ (irreducibles_finite H).toFinset,
        (c ψ * (centralInvolutionSign t ψ - ε)) • ψ) = 0 := by
      funext h
      have h1 := hpar h
      rw [hshift] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
      rw [Finset.mul_sum] at h1
      have h2 : ∑ ψ ∈ (irreducibles_finite H).toFinset,
          c ψ * (centralInvolutionSign t ψ - ε) * ψ h =
          ∑ ψ ∈ (irreducibles_finite H).toFinset, c ψ * centralInvolutionSign t ψ * ψ h -
            ∑ ψ ∈ (irreducibles_finite H).toFinset, ε * (c ψ * ψ h) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun ψ _ => by ring
      rw [h2, h1, sub_self]
    have h1 : BlocksInnerProduct (∑ ψ ∈ (irreducibles_finite H).toFinset,
        (c ψ * (centralInvolutionSign t ψ - ε)) • ψ) χ = BlocksInnerProduct 0 χ := by
      rw [hzero]
    rw [blocksInnerProduct_sum_smul_left] at h1
    have h2 : ∑ ψ ∈ (irreducibles_finite H).toFinset,
        c ψ * (centralInvolutionSign t ψ - ε) * BlocksInnerProduct ψ χ =
        c χ * (centralInvolutionSign t χ - ε) := by
      rw [Finset.sum_eq_single χ]
      · rw [blocksInnerProduct_self_of_mem hχ, mul_one]
      · intro ψ hψ hne'
        rw [blocksInnerProduct_of_mem ((Set.Finite.mem_toFinset _).mp hψ) hχ, ite_eq_right hne',
          mul_zero]
      · intro hnot
        exact absurd ((Set.Finite.mem_toFinset _).mpr hχ) hnot
    have h3 : BlocksInnerProduct (0 : H → ℂ) χ = 0 := by
      simp [BlocksInnerProduct]
    rw [h2, h3] at h1
    rcases mul_eq_zero.mp h1 with h4 | h4
    · exact h4
    · exact absurd (sub_eq_zero.mp h4) hne
  · intro hcoef h
    rw [hshift, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hs : centralInvolutionSign t χ = ε
    · rw [hs]
      ring
    · rw [hcoef χ ((Set.Finite.mem_toFinset _).mp hχ) hs]
      ring

end CFSG.CentralInvolution
