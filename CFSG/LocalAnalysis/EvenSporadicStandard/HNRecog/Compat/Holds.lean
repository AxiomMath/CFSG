module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Coxeter555.Segev29
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FactsOfF5

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

section Cert


theorem segev29_holds : Segev29 := fun H _ a x y => Coxeter555.segev29_unfolded H a x y

theorem segevSection4_of_open (hO : AutExtOpen) (hC : CompatOpen) : HNRecog.SegevSection4 :=
  segevSection4_of_interface twoHSInterface hO hC segev29_holds

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
