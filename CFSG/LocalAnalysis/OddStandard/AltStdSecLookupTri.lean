module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupCons
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne

theorem exactShapeTrichotomy_of_lookup (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hOut : SporadicOuterOrderLeTwoSimple) :
    ExactShapeTrichotomy := by
  intro X _ _ t A m hm hK hO h
  rcases section_dichotomy hO h (by omega) with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rcases exactShape_almostSimple hlookup hHN hOut hK hO h hm h3 with h4 | h4
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr h4))

end CFSG.OddStandard.AltStdSec
