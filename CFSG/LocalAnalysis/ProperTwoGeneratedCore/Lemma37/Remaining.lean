module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Linear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzULinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem caseIJankoConfiguration_of_unitaryOuter
    (h78 : CaseIUnitaryOuterExcluded) :
    CaseIJankoConfiguration :=
  caseIJankoConfiguration_of_linear (caseILinear h78)

end CFSG.ProperTwoGeneratedCore.Lemma37
