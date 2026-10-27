module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.BM.BThirteen

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def InvFact (X T : MatB) : Prop :=
  T * T = 1 ∧ T ≠ 1 ∧ (T - 1).rank = 1860 ∧ T * X = X * T

@[expose] def Fact17150 (X T1 T2 T4 T5 G : MatB) : Prop :=
  X ^ 13 = 1 ∧ X ≠ 1 ∧ InvFact X T1 ∧ InvFact X T2 ∧ InvFact X T4 ∧ InvFact X T5 ∧
    T1 * T5 = T5 * T1 ∧ T5 ≠ T1 ∧ (T1 * T2) ^ 3 = 1 ∧ T1 * T2 ≠ 1 ∧
    G * X = X ^ 6 * G ∧ G * T1 = T1 * G ∧ G * T2 = T2 * G ∧ G * T5 = T5 * G ∧
    T4 * T2 * T1 * T4 ≠ T1 * T2 ∧ T2 * T4 * T1 * T2 ≠ T1 * T4 ∧ T2 * T5 * T1 * T2 ≠ T1 * T5 ∧
    T1 * T4 * T2 * T1 ≠ T2 * T4 ∧ T1 * T5 * T2 * T1 ≠ T2 * T5 ∧ T1 * T5 * T4 * T1 ≠ T4 * T5

end CFSG.KC.BM.BThirteen

end
