module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.ComponentClassification.GrSLit

@[expose] def IsL34Field {G : Type*} [Group G] (J : Subgroup G) (x : G) : Prop :=
  x ∈ normalizer (J : Set G) ∧ x * x = 1 ∧ x ∉ withKernel J ∧
    Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = 168 * Nat.card (zStarIn J)

@[expose] def L34CyclicFourCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
    ∀ y ∈ P, (∀ p ∈ P, p * y = y * p) → y ∈ zStarIn J

@[expose] def L34FieldSylowFusionFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (s : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsL34Field J s → IsSylowTwoIn P J →
    s ∈ normalizer (P : Set G) → Nat.card ↥(P ⊓ zStarIn J) = 2 →
    ∀ p ∈ P, p * s * (p * s) = 1 →
      ∃ q ∈ P, ∃ y ∈ P, (∀ r ∈ P, r * y = y * r) ∧ y * s = s * y ∧ q * (p * s) * q⁻¹ = y * s

end CFSG.ComponentClassification.HarrisLit.EndB
