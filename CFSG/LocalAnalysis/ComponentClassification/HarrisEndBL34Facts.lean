module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicFourCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFieldFusion

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

theorem l34CyclicFourCenterFact :
    L34CyclicFourCenterFact :=
  GrSLit.L34Facts.cyclicFourCenter

theorem l34FieldSylowFusionFact :
    L34FieldSylowFusionFact :=
  fun G _ _ J P s hJ hL hs hP hsP h2 => GrSLit.L34Facts.fieldSylowFusion G J P s hJ hL hs hP hsP h2

end CFSG.ComponentClassification.HarrisLit.EndB
