module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34CyclicCenterSylowFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
    ∀ a ∈ P ⊓ zStarIn J, orderOf a = 2 →
    ∃ A₀ : Subgroup G, A₀ ≤ P ∧ IsEightGroup A₀ ∧ a ∈ A₀ ∧
      (∀ c ∈ A₀, ∀ p ∈ P, c⁻¹ * p⁻¹ * c * p ∈ zpowers a) ∧
      ∀ B : Subgroup G, B ≤ P → (∀ u ∈ B, ∀ v ∈ B, u⁻¹ * v⁻¹ * u * v ∈ zStarIn J) →
        (∀ u ∈ B, u * u ∈ zStarIn J) →
        ∃ E : Subgroup G, E ≤ P ∧ A₀ ≤ E ∧ P ⊓ zStarIn J ≤ E ∧ B ≤ E ∧ Nat.card E = 64 ∧
          (∀ u ∈ E, ∀ v ∈ E, u⁻¹ * v⁻¹ * u * v ∈ zpowers a) ∧ ∀ u ∈ E, u * u ∈ zpowers a

end CFSG.ComponentClassification.GrSLit
