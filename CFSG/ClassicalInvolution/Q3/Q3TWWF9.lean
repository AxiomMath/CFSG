module

public import CFSG.ClassicalInvolution.Q3.Q3TWWordsTD
public import CFSG.ClassicalInvolution.Q3.Q3ZMat
public import CFSG.LieType.Multipliers.U43Field

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.ClassicalInvolution.Q3.Q3Z

@[expose] def frob9 (x : F9) : F9 := x ^ 3

@[expose] def rootMatF9 (i j : Fin 4) (c : F9) : Matrix (Fin 4) (Fin 4) F9 :=
  1 + Matrix.single i j c - Matrix.single (Fin.rev j) (Fin.rev i) (frob9 c)

@[expose] def longMatF9 (i : Fin 4) (c : F9) : Matrix (Fin 4) (Fin 4) F9 :=
  1 + Matrix.single i (Fin.rev i) c

@[expose] def iota9 : F9 := ⟨0, 1⟩

@[expose] def nF9 : Fin 12 → Matrix (Fin 4) (Fin 4) F9 :=
  ![longMatF9 0 iota9, longMatF9 3 (-iota9), longMatF9 1 iota9, longMatF9 2 (-iota9),
    rootMatF9 0 2 1, rootMatF9 0 2 iota9, rootMatF9 0 1 1, rootMatF9 0 1 iota9,
    rootMatF9 1 0 1, rootMatF9 1 0 iota9, rootMatF9 2 0 1, rootMatF9 2 0 iota9]

theorem su4_cube_F9 : ∀ i, nF9 i * nF9 i * nF9 i = 1 := by decide +kernel

theorem su4_rels_F9 : ∀ w ∈ su4Words, evalCube nF9 w = 1 := by decide +kernel

end CFSG.ClassicalInvolution.Q3.Q3TW
