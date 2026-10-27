module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoB

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (standardComponentOddCore)
open CFSG.ComponentClassification.RankTwoStandard

@[expose] def StepAS81TwoB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    standardComponentOddCore G = ⊥ → ChevalleyExceptionalModel A .G2 2 2 →
    AS81.Sec3Below (Nat.card G) →
    ∃ (z : rankTwoX A) (h : LargeExtraspecial.S14.PattersonCo1Hyp (rankTwoX A) z),
      Sporadic.Co1Patterson.NotWeaklyClosed h ∧ HoltFree.Co1TwoBData (rankTwoX A) z

end CFSG.ComponentClassification.RankTwoExceptional
