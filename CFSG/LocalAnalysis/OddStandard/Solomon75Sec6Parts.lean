module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def Sec6PumpUpHolds : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), SolCEx X → IsMaxAhatDeg X n → Sec6Lemma51 X n →
    Sec6PumpUp X n

@[expose] def Sec6CentralChoiceHolds : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (t : X), SolCEx X → ¬ HypA X → IsMaxAhatDeg X n →
    (n = 8 ∨ n = 11) → Sec6Lemma51 X n → IsSec6Choice X n t →
      ∃ t' : X, IsSec6Choice X n t' ∧ (K0 X n (cen t') ≠ ⊥ → t' ∈ K0 X n (cen t'))

@[expose] def Sec6TwoRankHolds : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (t : X), Sec6Setting X n t → 2 ≤ Open.twoRank X

end CFSG.OddStandard.Solomon75
