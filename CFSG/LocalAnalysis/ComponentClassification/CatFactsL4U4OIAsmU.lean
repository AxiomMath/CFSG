module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFAsm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILi
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUn

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

theorem outerL2Cent_of_O8 (hO8 : OuterInvCentO8) : OuterL2Cent :=
  outerL2Cent_of OIL.outerInvCentL4 OIU.outerInvCentU4 hO8

theorem outerL2Fusion_of_O8 (hO8 : OuterInvCentO8) : OuterL2Fusion :=
  outerL2Fusion_of OIL.outerInvCentL4 OIU.outerInvCentU4 hO8

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
