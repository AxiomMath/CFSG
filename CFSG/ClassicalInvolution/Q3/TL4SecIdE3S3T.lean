module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TC
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TL2
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TL3
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TU3
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TU33
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12A
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3MTAbel
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.TA3SOLCore
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreRank
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4E3MuPass
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2B3
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddFrGen
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4D
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4F
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Y
public import CFSG.ClassicalInvolution.Q3.TL4VtxFree
public import CFSG.Foundations
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem secIdE3S3NoTwist_proved : SecIdE3S3NoTwist :=
  secIdE3S3NoTwist_of twKindL2_proved twKindL3_proved (twKindU3_of twKindU33_proved)
    modelM12Acts3_proved

end CFSG.ClassicalInvolution.Q3.TL4
