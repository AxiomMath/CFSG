module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34InvolutionCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (t : G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → t * t = 1 → t ∈ normalizer (K : Set G) →
    ∃ w ∈ K, w * w = 1 ∧ w * t = t * w ∧ w ∉ zStarIn K ∧ w⁻¹ * t ∉ coreActionKernel K

@[expose] def L34UnbalancingOddCoreFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J →
    (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J)) →
    ¬ oddIn (J ⊓ centralizer ({x} : Set G)) ≤ oddIn J

@[expose] def L34UnbalancingFourFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J F : Subgroup G), GSUnbalancingTriple a x J →
    (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J)) →
    F ≤ normalizer (J : Set G) ⊓ centralizer ({x} : Set G) → IsPGroup 2 F → x ∈ F →
    F = omegaOne F → F ⊓ coreActionKernel J = ⊥ → pRank 2 ↥F ≤ 2 →
    IsElemTwo F ∧ Nat.card F ≤ 4

end CFSG.ComponentClassification.GrSLit
