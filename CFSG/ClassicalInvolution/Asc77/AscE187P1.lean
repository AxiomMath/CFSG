module

public import CFSG.ClassicalInvolution.Asc77.AscE187Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.centralizes_conj_of_mem_RSet_of (hc : ConjInvariant Ω)
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hl67 : ∀ (S₁ : Sylow 2 G) (X : Subgroup G), X ∈ RSet Ω → ∀ Y : Subgroup G, Y ∈ RSet Ω →
      X ≤ (S₁ : Subgroup G) → Y ≤ (S₁ : Subgroup G) → X ≠ Y → Commutes X Y)
    {S₁ : Sylow 2 G} {K₁ R₁ T : Subgroup G} {z₁ β : G}
    (hz₁ : IsUniqueInvolution K₁ z₁) (hR₁ : R₁ ∈ RSet Ω) (hR₁K₁ : R₁ ≤ K₁)
    (hR₁S : R₁ ≤ (S₁ : Subgroup G)) (hβ : β ∈ (S₁ : Subgroup G)) (hT : T ∈ RSet Ω)
    (hTS : T ≤ (S₁ : Subgroup G)) : ∀ y ∈ T, y * (β * z₁ * β⁻¹) = (β * z₁ * β⁻¹) * y := by
  intro y hy
  have hR₂ : IsPGroup 2 R₁ := by
    obtain ⟨J, -, -, h2, -⟩ := mem_RSet_iff.mp hR₁
    exact h2
  have hz₁R : z₁ ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz₁ hR₁K₁ hR₂
    (by have := h8R hR₁; omega)
  set T' := conjSub β⁻¹ T with hT'
  have hT'mem : T' ∈ RSet Ω := RSet.conj hc hT β⁻¹
  have hT'S : T' ≤ (S₁ : Subgroup G) := by
    intro x hx
    rw [hT', mem_conjSub_iff, inv_inv] at hx
    have h1 : β * x * β⁻¹ ∈ (S₁ : Subgroup G) := hTS hx
    have : x = β⁻¹ * (β * x * β⁻¹) * β := by group
    rw [this]
    exact S₁.mul_mem (S₁.mul_mem ((S₁ : Subgroup G).inv_mem hβ) h1) hβ
  have hy' : β⁻¹ * y * β ∈ T' := by
    rw [hT', mem_conjSub_iff, inv_inv]
    have : β * (β⁻¹ * y * β) * β⁻¹ = y := by group
    rw [this]
    exact hy
  have hcz : (β⁻¹ * y * β) * z₁ = z₁ * (β⁻¹ * y * β) := by
    by_cases hTR : T' = R₁
    · have hyR : β⁻¹ * y * β ∈ K₁ := hR₁K₁ (hTR ▸ hy')
      exact (hz₁.commute_of_mem hyR).symm
    · exact (hl67 S₁ T' hT'mem R₁ hR₁ hT'S hR₁S hTR) _ hy' z₁ hz₁R
  calc y * (β * z₁ * β⁻¹) = β * ((β⁻¹ * y * β) * z₁) * β⁻¹ := by group
    _ = β * (z₁ * (β⁻¹ * y * β)) * β⁻¹ := by rw [hcz]
    _ = (β * z₁ * β⁻¹) * y := by group


theorem centralizes_conj_of_mem_RSet (h : E187Hyps p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {S₁ : Sylow 2 G} {K₁ R₁ T : Subgroup G} {z₁ β : G}
    (hz₁ : IsUniqueInvolution K₁ z₁) (hR₁ : R₁ ∈ RSet Ω) (hR₁K₁ : R₁ ≤ K₁)
    (hR₁S : R₁ ≤ (S₁ : Subgroup G)) (hβ : β ∈ (S₁ : Subgroup G)) (hT : T ∈ RSet Ω)
    (hTS : T ≤ (S₁ : Subgroup G)) : ∀ y ∈ T, y * (β * z₁ * β⁻¹) = (β * z₁ * β⁻¹) * y := by
  exact E187C.centralizes_conj_of_mem_RSet_of hΩ.conjInvariant
    (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ)
    (fun S₁ X hX Y hY hXS hYS hXY => h.l67 hp hq G Ω hΩ S₁ X hX Y hY hXS hYS hXY)
    hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS

end CFSG.ClassicalInvolution.Asc77
