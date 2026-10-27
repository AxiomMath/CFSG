module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAltSix
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevU33
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTits
public import CFSG.LieType.ChevTwo.ModelSplitHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationOrdinary

public section

namespace CFSG.GroupTheory

theorem gomiChevAtomGeneration_holds :
    GomiChevAtomGeneration := by
  refine gomiChevAtomGeneration_of_simple fun K _ _ _ hc => ?_
  rcases CFSG.LieType.ChevTwo.chevTwoModelSplit_holds K hc with
    ⟨t, n, f, ht, hm⟩ | ⟨n, f, hm⟩ | he | hm
  · exact gomiAtomGenerationTop_of_lieModel ht hm
  · exact gomiAtomGenerationTop_of_lieModel_tits hm
  · exact gomiAtomGenerationTop_of_mulEquiv_alternatingGroup_six he.some
  · exact gomiAtomGenerationTop_of_psu_three_three hm

end CFSG.GroupTheory
