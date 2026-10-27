module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Lin
public import CFSG.GH74.Generic.BProg.B2.GenLocL4InnerFinal
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Out

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint

namespace GenLocL4Final

theorem outerStmt (F : Type) [Field F] [Finite F] : GenLocL4Lin.Sl4OuterStmt F :=
  fun hF hF4 h7 {_} _ _ α hA hout hsect => gammaAct_sl4_outer hF hF4 h7 α hA hout hsect

end GenLocL4Final

section Final

variable {F : Type} [Field F] [Finite F]

theorem gammaAct_sl4_lin (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hA : IsRank23 A) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ :=
  gammaAct_sl4_lin_of_classes hF4 h7 (GenLocL4Final.quatStmt F) (GenLocL4Final.outerStmt F) α hA hsect

theorem genLoc4_sl4_lin {J : Type} [Group J] (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 4) F) : GenLoc4 J :=
  genLoc4_sl4_lin_of_classes hF4 h7 (GenLocL4Final.quatStmt F) (GenLocL4Final.outerStmt F) e

end Final

theorem genLoc4_l4_lin {J : Type} [Group J] {p f : ℕ} (hJ : LieModel J .PSL 4 p f)
    (hq4 : p ^ f % 4 = 3) (hq7 : 7 ≤ p ^ f) : GenLoc4 J :=
  genLoc4_l4_lin_of_classes hJ hq4 hq7 GenLocL4Final.quatStmt GenLocL4Final.outerStmt

theorem genLoc4_l4_lin_of_gt_three {J : Type} [Group J] {p f : ℕ} (hJ : LieModel J .PSL 4 p f)
    (h3 : 3 < p ^ f) (hq4 : p ^ f % 4 = 3) : GenLoc4 J :=
  genLoc4_l4_lin hJ hq4 (by omega)

end CFSG.GH74.Generic.BProg.B2
