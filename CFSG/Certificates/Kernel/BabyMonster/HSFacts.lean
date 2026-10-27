module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.HigmanSims

public section

namespace CFSG.KC.BM.HS

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def hsA (G1 G2 : MatB) : MatB :=
  G2 ^ 15 * G2 ^ 15 * (G1 * G2 ^ 15 * G1 ^ 3) ^ 12

@[expose] def hsB (G1 G2 : MatB) : MatB := G2 ^ 15 * (G1 * G2 ^ 15 * G1 ^ 3) ^ 9

@[expose] def letter {M : Type*} [Monoid M] (A B : M) (l : ℕ × Bool) : M :=
  if l.1 = 0 then A else if l.2 then B else B ^ 4

@[expose] def relVal {M : Type*} [Monoid M] (A B : M) (v : List (ℕ × Bool)) : M :=
  (v.map (letter A B)).prod

@[expose] def Fact17535 (G1 G2 : MatB) : Prop :=
  hsA G1 G2 * hsA G1 G2 = 1 ∧ hsA G1 G2 ≠ 1 ∧ hsB G1 G2 ^ 5 = 1 ∧
    hsA G1 G2 * G2 ^ 14 = G2 ^ 14 * hsA G1 G2 ∧ hsB G1 G2 * G2 ^ 14 = G2 ^ 14 * hsB G1 G2 ∧
    ∀ v ∈ TauCeti.Sporadic.hsPresentation.relatorLetters, relVal (hsA G1 G2) (hsB G1 G2) v = 1

end CFSG.KC.BM.HS

end
