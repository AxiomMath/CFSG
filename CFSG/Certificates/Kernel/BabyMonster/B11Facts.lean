module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.BM.B11

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def Fact17706 (Y X0 X1 X2 X3 : MatB) : Prop :=
  Y ^ 11 = 1 ∧ Y ≠ 1 ∧ X0 * X0 = 1 ∧ X1 * X1 = 1 ∧ X2 * X2 = 1 ∧ X3 * X3 = 1 ∧
    X0 * X1 * X0 = X1 * X0 * X1 ∧ X1 * X2 * X1 = X2 * X1 * X2 ∧ X2 * X3 * X2 = X3 * X2 * X3 ∧
    X0 * X2 = X2 * X0 ∧ X0 * X3 = X3 * X0 ∧ X1 * X3 = X3 * X1 ∧
    X0 * Y = Y * X0 ∧ X1 * Y = Y * X1 ∧ X2 * Y = Y * X2 ∧ X3 * Y = Y * X3 ∧
    X0 * X2 ≠ 1 ∧ (X0 - 1).rank = 1860 ∧ (X0 * X2 - 1).rank = 2048

end CFSG.KC.BM.B11

end
