module

public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.B.Final.Basic
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Monster.GMS

@[expose] def BabyTwoDFiveAFact : Prop :=
  ∃ t y : CFSG.Blueprint.NativeSporadic.B, BabyInv 2 t ∧ orderOf y = 5 ∧ y * t = t * y ∧
    Matrix.rank (CFSG.Monster.B.bMat y - 1) = 3480

end CFSG.LocalAnalysis.GLTheoremA.H1017
