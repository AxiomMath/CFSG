module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFMain
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFEven
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4Conn278ANMu
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird
public import CFSG.ClassicalInvolution.Q3.TL4OddSecEdge
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.Q3.TL4VtxFamC
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem omegaAutOddFreeR_of_small (hSp : OuterFixedOddFree .PSp 2)
    (hL : OuterFixedOddFree .PSL 4) (hU : OuterFixedOddFree .PSU 4) (hD : D4OuterAutOddFree) :
    OmegaAutOddFreeR :=
  omegaAutOddFreeR_of_outer hSp hL hU (fun _ hk => outerFixedOddFree_pOmegaPlus hk)
    (fun _ hk => outerFixedOddFree_pOmegaMinus hk) hD

end CFSG.ClassicalInvolution.Q3.TL4
