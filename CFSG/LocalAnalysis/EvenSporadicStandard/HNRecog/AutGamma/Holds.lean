module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FactsOfF5

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

section Cert


theorem segevSection5_holds : HNRecog.SegevSection5 :=
  segevSection5_of_twoHSInterface twoHSInterface

end Cert

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
