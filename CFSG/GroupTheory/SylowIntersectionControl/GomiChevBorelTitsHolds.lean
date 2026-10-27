module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevBorelTitsSimple
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevU33
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTits
public import CFSG.LieType.ChevTwo.ModelSplitHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAltSix

public section

namespace CFSG.GroupTheory

theorem gomiChevBorelTits_holds :
    GomiChevBorelTits := by
  refine gomiChevBorelTits_of_simple fun K _ _ _ hc => ?_
  rcases CFSG.LieType.ChevTwo.chevTwoModelSplit_holds K hc with
    ⟨t, n, f, ht, hm⟩ | ⟨n, f, hm⟩ | he | hm
  · exact CFSG.LieType.BorelTits.holds_of_lieModel hm ht
  · exact holds_two_of_lieModel_tits hm
  · exact holds_two_of_mulEquiv_alternatingGroup_six he.some
  · exact holds_two_of_psu_three_three hm

end CFSG.GroupTheory
