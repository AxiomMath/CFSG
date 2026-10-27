module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34GraphInvertModStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    (∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g) →
    ∀ B : Subgroup G, B ≤ S ⊓ J → IsEightGroup B → B ⊓ zStarIn J = zpowers a →
      S ≤ normalizer (B : Set G) →
      (∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
        y ∈ B ⊔ (S ⊓ zStarIn J)) →
      (∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
        n⁻¹ * (b : G) * n = (σ b : G)) →
      ∀ c ∈ S, c * c = 1 → c ∉ withKernel J →
        S ⊓ centralizer (B : Set G) = S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c →
        ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c * s ∈ zStarIn J

@[expose] def L34GraphInvertCoverFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J S B : Subgroup G) (c : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn (S ⊓ J) J → S ≤ normalizer (J : Set G) →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 → B ≤ S ⊓ J →
    (∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
      y ∈ B ⊔ (S ⊓ zStarIn J)) →
    c ∈ S → c * c = 1 → c ∉ withKernel J → (∀ b ∈ B, c * b = b * c) →
    ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c * s ∈ zStarIn J

@[expose] def L34GraphInvertGlobalStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    (∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g) →
    ∀ B : Subgroup G, B ≤ S ⊓ J → IsEightGroup B → B ⊓ zStarIn J = zpowers a →
      S ≤ normalizer (B : Set G) →
      (∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
        y ∈ B ⊔ (S ⊓ zStarIn J)) →
      (∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
        n⁻¹ * (b : G) * n = (σ b : G)) →
      ∀ c ∈ S, c * c = 1 → c ∉ withKernel J →
        S ⊓ centralizer (B : Set G) = S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c →
        (∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c * s ∈ zStarIn J) →
        (∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), ∀ t ∈ S ⊓ J ⊓ centralizer (B : Set G),
          s * t = t * s) ∧ ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c = s⁻¹

end CFSG.ComponentClassification.GrSLit
