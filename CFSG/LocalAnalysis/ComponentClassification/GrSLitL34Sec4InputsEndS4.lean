module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34CyclicCentralEightFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (a : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 → a ∈ P ⊓ zStarIn J →
    a * a = 1 → a ≠ 1 →
    ∃ B : Subgroup G, B ≤ P ∧ IsEightGroup B ∧ B ⊓ zStarIn J = zpowers a ∧
      (∀ y ∈ P, y ∈ B ↔ y * y = 1 ∧ ∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ∧
      (∀ y ∈ P, (∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ B ⊔ (P ⊓ zStarIn J)) ∧
      B ≤ closure {t | ∃ s ∈ P ⊓ centralizer (B : Set G), t = s * s}

@[expose] def L34EightTransvectionFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P E : Subgroup G) (a : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
    E ≤ P → IsEightGroup E → E ⊓ zStarIn J = zpowers a →
    ∀ τ : ↥E ≃* ↥E, (∀ y : ↥E, (y : G)⁻¹ * (τ y : G) ∈ zpowers a) →
      ∃ p ∈ P ⊓ normalizer (E : Set G), ∀ y : ↥E, p⁻¹ * (y : G) * p = (τ y : G)

@[expose] def L34OutSquareFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → ∀ s ∈ normalizer (J : Set G),
      IsPGroup 2 ↥(zpowers s) → s * s ∈ withKernel J

end CFSG.ComponentClassification.GrSLit
