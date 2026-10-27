module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutDa

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_sl4_outer {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hA : IsRank23 A) (hout : ∃ a : A, ¬ GenLocL4Out.IsInnerDiag4 (α a))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ := by
  have _ := hF
  exact GenLocL4Out.gammaAct_sl4_outer_of_classes (GenLocL4Out.classExt F) (GenLocL4Out.classDb F)
    (GenLocL4Out.classDa F) hF4 h7 α hA hout hsect

end CFSG.GH74.Generic.BProg.B2
