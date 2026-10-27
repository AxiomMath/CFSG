module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415SimpleInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxSmall

public section

namespace CFSG.ComponentClassification.HarrisLit

theorem twoJ2OuterInvolutionIndexFact_holds :
    TwoJ2OuterInvolutionIndexFact :=
  CFSG.ComponentClassification.GrSLit.L34Facts.twoJ2OuterInvolutionIndex

theorem twoHSInnerInvolutionIndexFact_holds :
    TwoHSInnerInvolutionIndexFact :=
  CFSG.ComponentClassification.GrSLit.L34Facts.twoHSInnerInvolutionIndex

theorem harris415SmallTypesIndexFact_holds :
    Harris415SmallTypesIndexFact :=
  CFSG.ComponentClassification.GrSLit.L34Facts.harris415SmallTypesIndex

end CFSG.ComponentClassification.HarrisLit
