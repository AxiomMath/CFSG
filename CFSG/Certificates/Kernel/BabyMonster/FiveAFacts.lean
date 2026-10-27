module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.BM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def uWord (X H : MatB) : MatB :=
  (H ^ 7 * X * H) * H ^ 4 * (H ^ 7 * X ^ 4 * H) *
    ((H ^ 5 * X * H ^ 3) * H ^ 4 * (H ^ 5 * X ^ 4 * H ^ 3)) * (X * H ^ 4 * X ^ 4) * H ^ 4

@[expose] def Fact13610 (X H : MatB) : Prop :=
  (H ^ 4 - 1).rank = 2048 ∧ uWord X H * uWord X H = 1 ∧ uWord X H ≠ 1 ∧
    (uWord X H - 1).rank = 2048

@[expose] def qOneW (X H : MatB) : MatB := (X * H ^ 3) ^ 8

@[expose] def qTwoW (X H : MatB) : MatB := H ^ 7 * qOneW X H * H

@[expose] def qThreeW (X H : MatB) : MatB := X ^ 4 * qOneW X H * X

@[expose] def Fact13612 (X H : MatB) : Prop :=
  H ^ 4 * (qTwoW X H * qThreeW X H) = (qTwoW X H * qThreeW X H) * H ^ 4 ∧
    (qTwoW X H * qThreeW X H - 1).rank = 3480 ∧
    (qOneW X H ^ 4 * qTwoW X H ^ 4 * qOneW X H * qTwoW X H - 1).rank = 3500

end CFSG.KC.BM.FiveA

end
