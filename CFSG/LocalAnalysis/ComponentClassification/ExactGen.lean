module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenU35
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenJ2

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2


theorem exactGenerationInput_holds : ExactGenerationInput :=
  exactGenerationInput_of_core (fun S _ _ h => exactCore_U35 S h)
    (fun S _ _ h => exactCore_PSp45 S h) (fun S _ _ h => exactCore_J2 S h)

end CFSG.ComponentClassification.SolMax.SwapP2
