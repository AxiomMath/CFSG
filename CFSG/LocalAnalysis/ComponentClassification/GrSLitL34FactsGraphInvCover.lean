module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGraphInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndG3

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

theorem l34GraphInvertCoverFact :
    L34GraphInvertCoverFact :=
  fun _ _ _ _ _ _ _ hJ hL hP hSN hcyc h4 hBP hB hcS hc2 hcK hcB =>
    graphInvertModZ_inf hJ hL hP hSN hcyc h4 hBP hB hcS hc2 hcK hcB

end CFSG.ComponentClassification.GrSLit.L34Facts
