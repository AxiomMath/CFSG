module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultThree
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def ONMultThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .ONan →
    Nat.card (center X) ∣ 3

theorem OddMultThree.on_of_multThree (h : ONMultThree) : OddMultThree .ONan :=
  fun L _ _ hq _ hL => h L hq hL

end CFSG.EvenSporadicStandard.Induction
