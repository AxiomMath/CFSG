module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSPrime

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem mul_mem_of_relIndex_two {H K : Subgroup G} (hHK : H.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  have h := mul_mem_iff_of_index_two (H := H.subgroupOf K) hHK (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa only [mem_subgroupOf, Subgroup.coe_mul] using h

theorem index_two_ext [Finite G] {T₁ M : Subgroup G} {t y : G} (hMT : M ≤ T₁)
    (hM : M.relIndex T₁ = 2) (htT : t ∈ T₁) (htM : t ∉ M) (hyN : y ∈ normalizer (T₁ : Set G))
    (hyT : y ∉ T₁) (hyM : ∀ m ∈ M, y * m * y⁻¹ ∈ M) (hy2 : y * y ∈ M) :
    M ⊔ zpowers y ≤ T₁ ⊔ zpowers y ∧ (M ⊔ zpowers y).relIndex (T₁ ⊔ zpowers y) = 2 ∧
      (∀ h ∈ T₁ ⊔ zpowers y, ∀ x ∈ M ⊔ zpowers y, h * x * h⁻¹ ∈ M ⊔ zpowers y) ∧
      t ∉ M ⊔ zpowers y := by
  have hyNM : y ∈ normalizer (M : Set G) := mem_normalizer_of_maps hyM
  have hy2T : y * y ∈ T₁ := hMT hy2
  have hMT₂ : M ⊔ zpowers y ≤ T₁ ⊔ zpowers y := sup_le_sup_right hMT _
  have memM₂ : ∀ g, g ∈ M ⊔ zpowers y ↔ g ∈ M ∨ g * y⁻¹ ∈ M := fun g =>
    mem_sup_zpowers_iff hyNM hy2
  have memT₂ : ∀ g, g ∈ T₁ ⊔ zpowers y ↔ g ∈ T₁ ∨ g * y⁻¹ ∈ T₁ := fun g =>
    mem_sup_zpowers_iff hyN hy2T
  have hyinv : y⁻¹ ∉ T₁ := fun h => hyT (by simpa using T₁.inv_mem h)
  have htM₂ : t ∉ M ⊔ zpowers y := by
    rw [memM₂]
    rintro (h | h)
    · exact htM h
    · exact hyinv (by simpa using T₁.mul_mem (T₁.inv_mem htT) (hMT h))
  have hyty : y * t * y⁻¹ ∉ M := by
    intro h
    apply htM
    have := (mem_normalizer_iff.1 (inv_mem hyNM) _).1 h
    simpa [mul_assoc] using this
  have hytyT : y * t * y⁻¹ ∈ T₁ := (mem_normalizer_iff.1 hyN t).1 htT
  have htT₂ : t ∈ T₁ ⊔ zpowers y := mem_sup_left htT
  have hdvd : (M ⊔ zpowers y).relIndex (T₁ ⊔ zpowers y) ∣ 2 := by
    refine relIndex_dvd_two_iff.2 ⟨t, htT₂, fun b hb => ?_⟩
    rcases (memT₂ b).1 hb with hbT | hbT
    · rcases Classical.em (b ∈ M) with h | h
      · exact Or.inr (mem_sup_left h)
      · exact Or.inl (mem_sup_left (by
          rw [mul_mem_of_relIndex_two hM hbT htT]
          exact iff_of_false h htM))
    · rcases Classical.em (b * y⁻¹ ∈ M) with h | h
      · exact Or.inr ((memM₂ b).2 (Or.inr h))
      · refine Or.inl ((memM₂ _).2 (Or.inr ?_))
        have e : b * t * y⁻¹ = b * y⁻¹ * (y * t * y⁻¹) := by group
        rw [e, mul_mem_of_relIndex_two hM hbT hytyT]
        exact iff_of_false h hyty
  have hne1 : (M ⊔ zpowers y).relIndex (T₁ ⊔ zpowers y) ≠ 1 := fun h1 =>
    htM₂ (relIndex_eq_one.1 h1 htT₂)
  have hne0 : (M ⊔ zpowers y).relIndex (T₁ ⊔ zpowers y) ≠ 0 := by
    intro h0
    have := relIndex_mul_card (H := M ⊔ zpowers y) (K := T₁ ⊔ zpowers y)
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne this
  have hidx : (M ⊔ zpowers y).relIndex (T₁ ⊔ zpowers y) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  refine ⟨hMT₂, hidx, fun h hh x hx => ?_, htM₂⟩
  have hxT := hMT₂ hx
  have hhi := (T₁ ⊔ zpowers y).inv_mem hh
  rw [mul_mem_of_relIndex_two hidx ((T₁ ⊔ zpowers y).mul_mem hh hxT) hhi,
    mul_mem_of_relIndex_two hidx hh hxT]
  constructor
  · intro h1
    have := (M ⊔ zpowers y).inv_mem (h1.2 hx)
    simpa using this
  · intro h1
    rw [iff_true_right hx]
    have := (M ⊔ zpowers y).inv_mem h1
    simpa using this

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
