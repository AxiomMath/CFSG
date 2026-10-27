module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def Harris82Lemma54 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwoQuasisimple X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsMTypeSchur p X → ∀ (τ : StatedLieTag) (n f : ℕ),
    Blueprint.LieModel (X ⧸ Open.fusionZStar X) τ n p f → 5 ≤ p ^ f →
    ¬ Blueprint.LieModel (X ⧸ Open.fusionZStar X) .PSL 2 p f →
    ∀ t : X, orderOf t = 2 → t ∈ Open.fusionZStar X →
      ∃ u : X, orderOf u = 2 ∧ u ∉ Open.fusionZStar X ∧ ∃ J₁ J₂ : Subgroup X,
        IsTwoComponentIn J₁ (centralizer {u}) ∧ IsTwoComponentIn J₂ (centralizer {u}) ∧
        J₁ ≠ J₂ ∧ u ∈ J₁ ∧ IsSLTwoOver (p ^ f) (↥J₁ ⧸ pPrimeCore 2 ↥J₁) ∧
        (∃ (τ' : StatedLieTag) (n' : ℕ),
          Blueprint.LieModel (↥J₂ ⧸ Open.fusionZStar ↥J₂) τ' n' p f) ∧
        (t ∈ J₂ ∨ t * u ∈ J₂)

@[expose] def Harris82Lemma58b : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsTwoQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsSimpleChevalleyOver p (K ⧸ Open.fusionZStar K) →
    ∀ z₁ z₂ : K, orderOf z₁ = 2 → z₁ ∈ center K → orderOf z₂ = 2 →
    (QuotientGroup.mk z₂ : K ⧸ pPrimeCore 2 K) ∉ center (K ⧸ pPrimeCore 2 K) →
    ∀ L₁ L₂ : Subgroup K, IsTwoComponentIn L₁ (centralizer {z₂}) →
    IsTwoComponentIn L₂ (centralizer {z₂}) → z₁ ∈ L₁ → z₂ ∈ L₂ → ∀ k : ℕ, 5 ≤ p ^ k →
    IsSLTwoOver (p ^ k) (↥L₁ ⧸ pPrimeCore 2 ↥L₁) →
      ((∃ (τ : StatedLieTag) (n : ℕ),
          Blueprint.LieModel (↥L₂ ⧸ Open.fusionZStar ↥L₂) τ n p k) →
        ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsCoverOf .POmegaOdd m p k 2 (K ⧸ pPrimeCore 2 K)) ∧
      (IsSLTwoOver (p ^ k) (↥L₂ ⧸ pPrimeCore 2 ↥L₂) →
        IsCoverOf .POmegaOdd 3 p k 2 (K ⧸ pPrimeCore 2 K))

@[expose] def Harris82Theorem1FieldThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
    IsMTypeSchur 3 ↥L → ∀ (τ : StatedLieTag) (n : ℕ),
      ¬ Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) τ n 3 1

end CFSG.ComponentClassification.HarrisLit.T1
