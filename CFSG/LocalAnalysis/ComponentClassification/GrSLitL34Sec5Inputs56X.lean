module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34OuterInvolutionCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K R P : Subgroup G) (w : G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K → P ≤ R → IsPGroup 2 R →
    R ≤ normalizer (K : Set G) → w ∈ R → w * w = 1 → w ∉ withKernel K →
    4 * Nat.card ↥(R ⊓ centralizer ({w} : Set G)) ≤ Nat.card R

@[expose] def L34CommutatorFourGroupFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
    ∃ Y : Subgroup G, Y ≤ P ∧ IsElemTwo Y ∧ Nat.card Y = 4 ∧ Y ⊓ zStarIn K = ⊥ ∧
      Y ≤ ⁅P, P⁆ ⊔ (P ⊓ zStarIn K) ∧
      ∀ y ∈ P, (∀ p ∈ P, p⁻¹ * y⁻¹ * p * y ∈ zStarIn K) → ∃ y' ∈ Y, y'⁻¹ * y ∈ zStarIn K

end CFSG.ComponentClassification.GrSLit
