module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34GraphInvertStep : Prop :=
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
        (∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), ∀ t ∈ S ⊓ J ⊓ centralizer (B : Set G),
          s * t = t * s) ∧ ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c = s⁻¹

@[expose] def L34GraphFinalStep : Prop :=
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
        Nonempty (↥(S ⊓ J ⊓ centralizer (B : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4)) →
        (∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), s * s = 1 → s ∈ B) →
        (∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c = s⁻¹) →
        normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G) ≤
          normalizer ((S ⊓ J ⊓ centralizer (B : Set G) : Subgroup G) : Set G) →
        normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G) ≤
          normalizer (B : Set G) →
        (∃ φ : ↥(normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G)) →*
            GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
          φ.ker = (centralizer (B : Set G)).subgroupOf
            (normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G))) →
        False

end CFSG.ComponentClassification.GrSLit
