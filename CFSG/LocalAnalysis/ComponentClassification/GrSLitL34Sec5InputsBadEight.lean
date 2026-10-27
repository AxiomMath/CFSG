module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma510BadEightStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
    (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
    ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → (∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) →
      ∀ S₁ : Subgroup G, IsSylowTwoIn S₁ (normalizer (K₁ : Set G)) → S ≤ S₁ →
      ∀ b ∈ S₁ ⊓ zStarIn K₁, orderOf b = 2 → (∀ s ∈ S₁, s * b = b * s) → pumpUp K₁ b = K₁ →
      (∀ A : Subgroup G, A ≤ withKernel K₁ → IsEightGroup A → wGroup A = ⊥) →
      ∀ v₀ : G, orderOf v₀ = 2 → K₁ ≤ centralizer ({v₀} : Set G) →
      IsL34Family (pumpUp K₁ v₀) v₀ → K₁ ⊔ oddIn (pumpUp K₁ v₀) = pumpUp K₁ v₀ → b ≠ v₀ →
      twoExp (zStarIn K₁) = 1 → twoExp (zStarIn (pumpUp K₁ v₀)) = 1 → twoExp (zStarIn L) = 2 →
      ∃ v : G, orderOf v = 2 ∧ K₁ ≤ centralizer ({v} : Set G) ∧
        ¬ oddIn (pumpUp K₁ v) ≤ (center ↥K₁).map K₁.subtype ∧
        ∃ E : Subgroup G, IsEightGroup E ∧ E ≤ coreActionKernel K₁ ∧ ∀ e ∈ E, e * v = v * e

end CFSG.ComponentClassification.GrSLit
