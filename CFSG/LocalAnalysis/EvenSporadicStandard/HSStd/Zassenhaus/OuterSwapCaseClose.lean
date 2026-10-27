module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseCloseDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd CFSG.Open

theorem card_alt_twelve_pump : Nat.card (alternatingGroup (Fin 12)) = 239500800 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
