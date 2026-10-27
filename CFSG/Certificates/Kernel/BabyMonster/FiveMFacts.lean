module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.BM.FiveM

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def yOneW (G1 G2 : MatB) : MatB := G1 * G2 ^ 15 * G1 ^ 3

@[expose] def aW (G1 G2 : MatB) : MatB := (yOneW G1 G2 * G2 ^ 15) ^ 5

@[expose] def bW (G1 G2 : MatB) : MatB := (G2 ^ 15 * yOneW G1 G2) ^ 5

@[expose] def Fact13613 (G1 G2 : MatB) : Prop :=
  (G2 ^ 14) ^ 5 = 1 ∧ G2 ^ 14 ≠ 1 ∧ (G2 ^ 14 - 1).rank = 3480 ∧
    aW G1 G2 * aW G1 G2 = 1 ∧ aW G1 G2 ≠ 1 ∧ (aW G1 G2 - 1).rank = 2048 ∧
    bW G1 G2 * bW G1 G2 = 1 ∧ bW G1 G2 ≠ 1 ∧ (bW G1 G2 - 1).rank = 2048 ∧
    aW G1 G2 * bW G1 G2 = bW G1 G2 * aW G1 G2 ∧ (aW G1 G2 * bW G1 G2 - 1).rank = 2048 ∧
    aW G1 G2 * G2 ^ 14 = G2 ^ 14 * aW G1 G2 ∧ bW G1 G2 * G2 ^ 14 = G2 ^ 14 * bW G1 G2

end CFSG.KC.BM.FiveM

end
