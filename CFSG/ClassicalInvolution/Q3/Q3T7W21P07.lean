module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21P06
public import CFSG.ClassicalInvolution.Q3.Q3SPN3Rows
public import CFSG.ClassicalInvolution.Asc77.AscC25W13
public import CFSG.ClassicalInvolution.Asc77.AscC5OM8GStmt
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTwelve
public import CFSG.ClassicalInvolution.Asc77.AscS22B
public import CFSG.ClassicalInvolution.Asc77.AscS24Alpha
public import CFSG.ClassicalInvolution.Asc77.AscT7XFin
public import CFSG.ClassicalInvolution.Balance.CentralizedDeltaBasic
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeA
public import CFSG.ClassicalInvolution.Q3.Q3T6LinMember
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A09
public import CFSG.ClassicalInvolution.SmallCases.NDBH5
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Timmesfeld.Moufang.Three

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7W21

open CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

theorem c21_2Three_proved (hE : Q3T7E.ThmEWithSylow3) (hHt : TwinFrameHyp51t)
    (hHu : TwinFrameHyp51u) : C21_2Three :=
  c21_2Three_of_spinGen3 hE hHt hHu Q3SPN3.spinGen3_proved

end CFSG.ClassicalInvolution.Q3.Q3T7W21
