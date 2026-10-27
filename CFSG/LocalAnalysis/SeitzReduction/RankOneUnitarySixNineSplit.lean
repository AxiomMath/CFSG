module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNine

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3SixNineFreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    ∀ v ∈ T, v ^ 2 = 1 → v ∉ szT₁ L T ⊔ zpowers t → v ∉ centralizer (R₂ : Set G) →
      ∀ u ∈ U₁, (u * v) ^ 2 = 1 → ∃ w ∈ U₁, w * v * w⁻¹ = u * v

@[expose] def U3SixNineConjInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    (∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) →
    (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁ →
    ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t ∧
      ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), g⁻¹ * t * g ≠ v

theorem u3SixNineInput_of_free_of_conj
    (hfree : U3SixNineFreeInput) (hconj : U3SixNineConjInput) : U3SixNineInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU hncyc hS hC
  obtain ⟨v, hvT, hv2, hvS, hv⟩ := hconj G L f t T R₂ U₁ h hS2 hR hU hncyc hS hC
  have hvC : v ∉ centralizer (R₂ : Set G) := fun hvC => by
    have hvU : v ∈ U₁ := hC (mem_inf.mpr ⟨mem_sup_right hvT, hvC⟩)
    have hvT₁ : v ∈ szT₁ L T := by rw [← hU.inf_eq h hR]; exact mem_inf.mpr ⟨hvU, hvT⟩
    exact hvS (mem_sup_left hvT₁)
  refine ⟨v, hvT, by rw [hv2]; exact one_mem _, hvS, fun g u hu hgu => ?_⟩
  have hx2 : (u * v) ^ 2 = 1 := by
    rw [← hgu, show (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ by rw [sq, sq]; group, h.sq_eq_one,
      mul_one, mul_inv_cancel]
  obtain ⟨w, hw, hwv⟩ := hfree G L f t T R₂ U₁ h hS2 hR hU v hvT hv2 hvS hvC u hu hx2
  have e : (g⁻¹ * w)⁻¹ * t * (g⁻¹ * w) = v := by
    calc (g⁻¹ * w)⁻¹ * t * (g⁻¹ * w) = w⁻¹ * (g * t * g⁻¹) * w := by group
      _ = w⁻¹ * (w * v * w⁻¹) * w := by rw [hgu, hwv]
      _ = v := by group
  obtain ⟨g', hg', hg't⟩ := h.exists_normalizer_szA₁_conj_of_outer_of_card_sylow hS2
    (g := g⁻¹ * w) (by rw [e]; exact hvT) (by rw [e]; exact hvS)
  exact hv g' hg' (by rw [hg't, e])

end CFSG.SeitzReduction.RankOne
