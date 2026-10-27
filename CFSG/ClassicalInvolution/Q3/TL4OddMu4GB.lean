module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4H
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4OA
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4GA
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayerLeaf
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9Nbhd
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XVertex
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
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.Q3.TL4VtxFree
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

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Proved

variable {r n : ℕ}

theorem tightE4LinkGenR_three : TightE4LinkGenR r n :=
  tightE4LinkGenR_of e4CoverOddFree_proved e4CoverGen_proved

theorem tightE4GenR_three : TightE4GenR 3 n :=
  tightE4GenR_of tightE4LinkGenR_three

end Proved

section Main

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightE4VtxSR_three (h9 : CITBelowU 3 2 n) : TightE4VtxSR 3 n :=
  tightE4VtxSR_of_cover e4CoverOddFree_proved h9

end Main

end CFSG.ClassicalInvolution.Q3.TL4
