module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit

@[expose] def L34Lemma510CoverInvolutionStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → (∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) →
      ∀ S₁ : Subgroup G, IsSylowTwoIn S₁ (normalizer (K₁ : Set G)) → S ≤ S₁ →
      u ∈ zStarIn K₁ → (∀ s ∈ S₁, s * u = u * s) →
      (∀ A : Subgroup G, A ≤ withKernel K₁ → IsEightGroup A → wGroup A = ⊥) →
      ∀ v₀ : G, orderOf v₀ = 2 → K₁ ≤ centralizer ({v₀} : Set G) →
      IsL34Family (pumpUp K₁ v₀) v₀ → K₁ ⊔ oddIn (pumpUp K₁ v₀) = pumpUp K₁ v₀ → u ≠ v₀ →
      twoExp (zStarIn K₁) = 1 → twoExp (zStarIn (pumpUp K₁ v₀)) = 1 → twoExp (zStarIn L) = 2 →
      ∃ z₁ ∈ S ⊓ coreActionKernel L, orderOf z₁ = 2 ∧ z₁ ≠ t ∧ z₁ ∈ K₁

end CFSG.ComponentClassification.GrSLit.GrS5S
