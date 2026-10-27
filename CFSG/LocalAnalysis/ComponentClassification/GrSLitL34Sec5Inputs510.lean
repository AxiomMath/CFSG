module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def L34Lemma510CentralStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → (∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1) →
    (∃ z : G, orderOf z = 2 ∧ z ≠ t ∧
      omegaOne (S ⊓ coreActionKernel L) = zpowers t ⊔ zpowers z) →
    (∃ y ∈ S ⊓ coreActionKernel L ⊓ L, ∃ s ∈ S, s * y ≠ y * s) →
    ∀ u ∈ L34UnbalancingSet L t S,
      (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
      ∃ u' ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u' = u' * s) ∧
        ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
          Nat.card ↥(oddIn L ⊓ centralizer ({u'} : Set G))

@[expose] def L34Lemma510InvolutionStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ → S ≤ normalizer (K₁ : Set G) →
      (∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) →
      ((IsL34Type (K₁ ⧸ Open.fusionZStar K₁) ∧ Odd (Nat.card ↥(zStarIn K₁))) ∨
        IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) →
      ∃ z₁ ∈ S ⊓ coreActionKernel L, orderOf z₁ = 2 ∧ z₁ ≠ t ∧ z₁ ∈ K₁

@[expose] def L34Lemma511UniqueStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
    (∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ → S ≤ normalizer (K₁ : Set G)

end CFSG.ComponentClassification.GrSLit
