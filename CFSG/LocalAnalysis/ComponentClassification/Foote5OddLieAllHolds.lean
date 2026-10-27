module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieAll
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRE7
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRTwE6

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

theorem oddLieOuterCoreInput_holds :
    OddLieOuterCoreInput :=
  oddLieOuterCoreInput_of_E7_twistedE6 Exc.SRE7.innerDiagCoreInput_E7_holds
    Exc.SRTwE6.twistedE6InnerCoreInput_holds

end CFSG.ComponentClassification.Foote5.OddLieCore
