module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeOrder

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3U1ElemStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G)
    (E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) →
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 → E ≤ (u3OmegaAction L T R₂ t).range →
    (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal →
    (∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) →
    (∀ r ∈ R₂, r ^ 2 = 1) ∧
      (∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G),
        ∀ y ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x * y * x⁻¹ * y⁻¹ ∈ R₂) ∧
      (∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x ^ 2 ∈ R₂) ∧
      ⁅u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)⁆ = R₂

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem exists_u3U₁_export_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    (hreg : HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range)
    (hst : U3U1ElemStatement) :
    ∃ U₁ : Subgroup G,
      normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (U₁ : Set G) ∧
      szT₁ L T ⊔ R₂ ≤ U₁ ∧ U₁ ≤ centralizer (R₂ : Set G) ∧ t ∉ U₁ ∧
      Nat.card U₁ = (2 ^ f) ^ 6 ∧ U₁ ⊓ szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ∧
      (∀ w ∈ szT₁ L T, ∃ u ∈ U₁, ∃ r ∈ R₂, u * t * u⁻¹ = r * w * t) ∧
      (∀ u ∈ U₁ ⊔ zpowers t, (R₂ ⊔ zpowers t).map (MulAut.conj u).toMonoidHom = R₂ ⊔ zpowers t →
        u ∈ szR (szT₁ L T) R₂ t) ∧
      (∀ r ∈ R₂, r ^ 2 = 1) ∧ (∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂) ∧
      (∀ x ∈ U₁, x ^ 2 ∈ R₂) ∧ ⁅U₁, U₁⁆ = R₂ ∧
      (∀ g : G, g * t * g⁻¹ ∉ U₁) ∧
      ∀ g : G, g * t * g⁻¹ ∈ U₁ ⊔ zpowers t → ∃ u ∈ U₁, g * t * g⁻¹ = u * t * u⁻¹ := by
  obtain ⟨E, hE, hEn, hEreg⟩ := hreg
  obtain ⟨hYU₁, hHU₁, htU₁, hUeq, hU₁R₁, hcov⟩ :=
    h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨hR₂2, hU₁c, hU₁2, hU₁'⟩ := hst G L f t T R₂ E h hS2 hR hc hΩ hE hEn hEreg
  refine ⟨u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), hYU₁, hHU₁, inf_le_right, htU₁,
    h.card_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg, hU₁R₁, hcov, fun u hu hut => ?_, hR₂2,
    hU₁c, hU₁2, hU₁', h.conj_t_not_mem_u3U₁_of_elem_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2,
    fun g hg => h.conj_t_of_mem_u3U₁_sup_of_elem_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2
      hU₁c hU₁2 g hg⟩
  rw [← hUeq] at hu
  exact h.mem_szR_of_mem_u3U_of_card_sylow hS2 hR hc hΩ hEreg hu hut

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
