module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.BM.TwoDFiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def Fact101702 (T Y : MatB) : Prop :=
  T * T = 1 ∧ T ≠ 1 ∧ Y ^ 5 = 1 ∧ Y ≠ 1 ∧ T * Y = Y * T ∧ (T - 1).rank = 2168 ∧
    (Y - 1).rank = 3480

end CFSG.KC.BM.TwoDFiveA

end
