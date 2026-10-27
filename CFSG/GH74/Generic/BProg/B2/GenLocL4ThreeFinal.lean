module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Final
public import CFSG.GH74.Generic.BProg.B2.GenLocL4InnerU
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Three
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeOut

public section

open CFSG CFSG.GH74
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2

theorem genLoc4_sl4_zmod3 : GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) := by
  intro A _ _ α hA hsect
  have hF4 : Nat.card (ZMod 3) % 4 = 3 := by rw [Nat.card_zmod]
  by_cases hin : ∀ c : A, GenLocL4Q.IsInnerDiag4 (α c)
  · exact Or.inl (gammaAct_sl4_inner_all hF4 α hA hin hsect)
  · exact genOrLoc_sl4_outer_three α hA (not_forall.1 hin) hsect

theorem genLoc4_sl4_three {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3) :
    GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F) :=
  genLoc4_of_zmod3 hF3 genLoc4_sl4_zmod3

theorem genLoc4_sl4_lin_all {F : Type} [Field F] [Finite F] (hF4 : Nat.card F % 4 = 3) :
    GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F) := by
  by_cases h7 : 7 ≤ Nat.card F
  · exact genLoc4_sl4_lin hF4 h7 (MulEquiv.refl _)
  · exact genLoc4_sl4_three (by omega)

end CFSG.GH74.Generic.BProg.B2
