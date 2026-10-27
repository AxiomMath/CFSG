module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris82Theorem2SLTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    ∀ W : Subgroup X, (∀ a ∈ W, a * a = 1) → Nat.card W = 4 →
    ∀ z₁ ∈ W, ∀ z₂ ∈ W, z₁ ≠ 1 → z₂ ≠ 1 → z₁ ≠ z₂ → ∀ L₁ L₂ : Subgroup X,
      IsTwoComponentIn L₁ (centralizer (W : Set X)) →
      IsTwoComponentIn L₂ (centralizer (W : Set X)) → z₁ ∈ L₁ → z₂ ∈ L₂ →
      ∀ p : ℕ, p.Prime → p ≠ 2 → IsMTypeSchur p ↥L₁ → IsMTypeSchur p ↥L₂ →
      (∃ k : ℕ, Blueprint.LieModel (↥L₁ ⧸ Open.fusionZStar ↥L₁) .PSL 2 p k) →
        Blueprint.Catalog X

@[expose] def Harris82Theorem3SLTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card W = 4 →
    ∀ (L : Subgroup G) (p : ℕ), p.Prime → p ≠ 2 → IsTwoComponentIn L (centralizer (W : Set G)) →
      IsMTypeSchur p ↥L → ∀ k : ℕ, 1 ≤ k → 5 ≤ p ^ k →
      IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) → ∀ w ∈ L ⊓ W, w ≠ 1 →
        IsTwoComponentIn (GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})))
          (centralizer {w})

end CFSG.ComponentClassification.HarrisLit
