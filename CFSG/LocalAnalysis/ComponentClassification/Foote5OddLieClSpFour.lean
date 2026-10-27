module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpFourSplit
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpFourNs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpFam

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG

theorem ClSp.spFourThreeSkewInput : ClSp.SpFourThreeSkewInput := by
  intro K _ _ h3 _ A hA R hRodd hRi hRc
  refine ClSp.commute_of_eq_one ?_
  rcases hA with rfl | ⟨d, hd0, hd, rfl⟩
  · exact ClSp.eq_one_skewSplit_three h3 hRodd hRi hRc
  · exact ClSp.eq_one_skewNs_three h3 hd hd0 hRodd hRi hRc

theorem oddLieCoreFamilyInput_psp : OddLieCoreFamilyInput .PSp :=
  oddLieCoreFamilyInput_psp_of ClSp.spFourThreeSkewInput

end CFSG.ComponentClassification.Foote5.OddLieCore
