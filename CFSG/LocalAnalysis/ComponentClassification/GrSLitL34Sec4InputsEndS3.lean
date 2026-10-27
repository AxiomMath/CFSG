module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open Matrix

@[expose] def L34CyclicInvolutionClassFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
    ∀ u ∈ J, ∀ v ∈ J, u * u = 1 → v * v = 1 → u ∉ zStarIn J → v ∉ zStarIn J →
      ∃ j ∈ J, j⁻¹ * u * j = v

@[expose] def L34EndGL32Step : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) →
    (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
    (∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g) →
    ∃ B : Subgroup G, B ≤ S ⊓ J ∧ IsEightGroup B ∧ B ⊓ zStarIn J = zpowers a ∧
      S ≤ normalizer (B : Set G) ∧
      (∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
        y ∈ B ⊔ (S ⊓ zStarIn J)) ∧
      ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B, n⁻¹ * (b : G) * n = (σ b : G)

@[expose] def L34EndTStep : Prop :=
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
      ∀ T : Subgroup G, T = S ⊓ centralizer (B : Set G) →
        (Nonempty (↥T ≃* Multiplicative (Fin 3 → ZMod 4)) ∧
          centralizer (T : Set G) ≤ T ⊔ oddIn (normalizer (T : Set G)) ∧
          ∃ φ : ↥(normalizer (T : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
            φ.ker = (T ⊔ oddIn (normalizer (T : Set G))).subgroupOf (normalizer (T : Set G))) ∨
        ∃ c ∈ S, c * c = 1 ∧ c ∉ withKernel J ∧ T = S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c

@[expose] def L34EndGraphStep : Prop :=
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
        S ⊓ centralizer (B : Set G) = S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c → False

end CFSG.ComponentClassification.GrSLit
