module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Holt.SL6

open scoped MatrixGroups

@[expose] def stdTransvection : SL(6, ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 6)) (j := 5) (by decide) 1

theorem coe_stdTransvection :
    (stdTransvection : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + Matrix.single 0 5 1 :=
  Matrix.SpecialLinearGroup.transvection_coe _ _

end CFSG.Holt.SL6
