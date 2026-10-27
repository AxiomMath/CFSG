module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXGlobal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

structure TabXFacts {G : Type} [Group G] (a z b z₁ : G) (R : Subgroup G) : Prop where
  R_le : R ≤ Gx z
  card_R : Nat.card ↥R = 256
  base : {c | IsConj b c ∧ c ∈ Gx z}.ncard = 120
  card_D : Nat.card ↥(derivedOf (Gx z)) = 7680
  card_DR : Nat.card ↥(derivedOf (Gx z) ⊓ R) = 128
  card_DRs : Nat.card ↥(derivedOf (Gx z) ⊔ R) = 15360
  quot : ∃ g₁ ∈ Gx z, ∃ g₂ ∈ Gx z, g₁ * g₁ ∈ derivedOf (Gx z) ∧ g₂ * g₂ ∈ derivedOf (Gx z) ∧
    g₁ ∉ derivedOf (Gx z) ∧ g₂ ∉ derivedOf (Gx z) ∧ g₁ * g₂⁻¹ ∉ derivedOf (Gx z)
  centre : centerOf (derivedOf (Gx z)) = centerOf (derivedOf (Gx z) ⊓ R) ∧
    Nonempty (↥(centerOf (derivedOf (Gx z))) ≃* Z 2 × Z 4)
  rows : ∃ c : Fin 2 → G, (∀ i, c i ∈ tabXSet a z b z₁ i) ∧
    (∀ i, Nat.card ↥(Gx z ⊓ Gx (c i)) = ![768, 384] i) ∧
    c 0 ∈ R ∧ Nat.card ↥(Gx z ⊓ Gx (c 0) ⊓ R) = 2 ^ 7 ∧
    Nat.card ↥(Gx z ⊓ Gx (c 0) ⊓ R ⊓ derivedOf (Gx z)) = 2 ^ 6 ∧
    Nat.card ↥(Gx z ⊓ Gx (c 0) ⊓ derivedOf (Gx z)) = 2 ^ 6 * 3 ∧
    c 1 ∉ R ∧ IsElemTwo 5 (Gx z ⊓ Gx (c 1) ⊓ R) ∧
    IsElemTwo 4 (Gx z ⊓ Gx (c 1) ⊓ R ⊓ derivedOf (Gx z)) ∧
    Nat.card ↥(Gx z ⊓ Gx (c 1) ⊓ derivedOf (Gx z)) = 2 ^ 5 * 3 ∧
    (∃ m₁ ∈ Gx z ⊓ Gx (c 1) ⊓ derivedOf (Gx z), ∃ m₂ ∈ Gx z ⊓ Gx (c 1) ⊓ derivedOf (Gx z),
      m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∉ R) ∧
    ∃ σ₀ ∈ Gx z, orderOf σ₀ = 3 ∧ ∃ t ∈ Gx z, t * σ₀ * t⁻¹ = σ₀⁻¹ ∧
      R ⊓ Gx σ₀ = Subgroup.closure ((centerOf (derivedOf (Gx z)) : Set G) ∪ {c 0}) ∧
      derivedOf (Gx z) ⊓ R ⊓ Gx σ₀ = centerOf (derivedOf (Gx z))

theorem tableX_of_facts {G : Type} [Group G] [Finite G] {a z b z₁ : G} {R : Subgroup G}
    (ha : a ∈ Subgroup.center G)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hK : IsShapeK ↥(_root_.commutator G ⊓ Gx z)) (hX : Nat.card ↥(Gx z) = 30720)
    (hR : CFSG.Open.pCoreOf 2 (Gx z) = R) (h : TabXFacts a z b z₁ R) : TableXData a z b z₁ := by
  subst hR
  obtain ⟨-, hRc, hB, hD, hDR, hDRs, ⟨g₁, hg₁, g₂, hg₂, hs₁, hs₂, hn₁, hn₂, hn₁₂⟩, hZ,
    ⟨c, hc, hstab, h0R, h0a, h0b, h0c, h1R, h1a, h1b, h1c, ⟨m₁, hm₁, m₂, hm₂, hcomm⟩,
      σ₀, hσ₀, hσ₀o, t, ht, htσ, hCR, hCD⟩⟩ := h
  exact tableX_of_data ha hnc hK hX hB c hc hstab hRc hD hDR hDRs hg₁ hg₂ hs₁ hs₂ hn₁ hn₂ hn₁₂
    h0R h0a h0b h0c h1R h1a h1b h1c hm₁ hm₂ hcomm hZ hσ₀ hσ₀o ht htσ hCR hCD

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
