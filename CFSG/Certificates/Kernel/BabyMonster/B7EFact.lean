module

public import CFSG.Certificates.Kernel.BabyMonster.SevenFacts

public section

namespace CFSG.KC.BM.SevenFacts

open CFSG.KC.BM

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def Fact16962Of (Al X Y T1 T2 E : MatB) : Prop :=
  Al * Al = 1 ∧ Al ≠ 1 ∧ (Al - 1).rank = 1860 ∧ Al * X = X * Al ∧ Al * Y = Y * Al ∧
    Al * T1 = T1 * Al ∧ Al * T2 = T2 * Al ∧ Al * E = E * Al ∧
    X ^ 7 = 1 ∧ X ≠ 1 ∧ Y ^ 5 = 1 ∧ Y ≠ 1 ∧ X * Y = Y * X ∧
    T1 * T1 = 1 ∧ T1 ≠ 1 ∧ T2 * T2 = 1 ∧ T2 ≠ 1 ∧ T1 ≠ T2 ∧ T1 * T2 = T2 * T1 ∧
    T1 * X = X * T1 ∧ T2 * X = X * T2 ∧ (T1 - 1).rank = 1860 ∧ (T2 - 1).rank = 1860 ∧
    (T1 * T2 - 1).rank = 2048 ∧ (Al * T1 - 1).rank = 2158 ∧ T1 ≠ Al ∧ T2 ≠ Al ∧
    E ^ 3 = 1 ∧ E ≠ 1 ∧ E * X = X * E ∧ E * T1 = T1 * E ∧
    (T1 * E) ^ 6 = 1 ∧ (T1 * E) ^ 3 = T1 ∧ T1 * E * (T1 * E) ≠ 1 ∧ T1 * E * (T1 * E) ≠ Al ∧
    T1 * Y ≠ Y * T1 ∧ T1 * Y ≠ Al * Y * T1

end CFSG.KC.BM.SevenFacts

end
