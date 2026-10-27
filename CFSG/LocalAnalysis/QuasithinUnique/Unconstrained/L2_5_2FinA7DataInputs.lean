module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.Unc25G2.A7
open Equiv

@[expose] def cyc (cs : List (List ℕ)) : Perm (Fin 7) :=
  (cs.map (fun c => (c.map (fun i => (Fin.ofNat 7 i))).formPerm)).prod

@[expose] def P0l : List (Perm (Fin 7)) :=
  [cyc [],
    cyc [[2, 3], [4, 5]],
    cyc [[0, 1], [4, 5]],
    cyc [[0, 1], [2, 3]],
    cyc [[0, 2], [1, 3]],
    cyc [[0, 2, 1, 3], [4, 5]],
    cyc [[0, 3, 1, 2], [4, 5]],
    cyc [[0, 3], [1, 2]]]

@[expose] def aP : Perm (Fin 7) := cyc [[0, 1], [2, 3]]

@[expose] def bP : Perm (Fin 7) := cyc [[0, 2], [1, 3]]

@[expose] def c1P : Perm (Fin 7) := cyc [[1, 2, 3]]

@[expose] def c2P : Perm (Fin 7) := cyc [[4, 5, 6]]

@[expose] def V0l : List (Perm (Fin 7)) := [1, aP, bP, aP * bP]

@[expose] def T0l : List (Perm (Fin 7)) := [1, c2P, c2P * c2P]

@[expose] def K1l : List (Perm (Fin 7)) :=
  [cyc [],
    cyc [[2, 3], [4, 5]],
    cyc [[1, 2], [4, 5]],
    cyc [[1, 2, 3]],
    cyc [[1, 3, 2]],
    cyc [[1, 3], [4, 5]],
    cyc [[0, 1], [4, 5]],
    cyc [[0, 1], [2, 3]],
    cyc [[0, 1, 2]],
    cyc [[0, 1, 2, 3], [4, 5]],
    cyc [[0, 1, 3, 2], [4, 5]],
    cyc [[0, 1, 3]],
    cyc [[0, 2, 1]],
    cyc [[0, 2, 3, 1], [4, 5]],
    cyc [[0, 2], [4, 5]],
    cyc [[0, 2, 3]],
    cyc [[0, 2], [1, 3]],
    cyc [[0, 2, 1, 3], [4, 5]],
    cyc [[0, 3, 2, 1], [4, 5]],
    cyc [[0, 3, 1]],
    cyc [[0, 3, 2]],
    cyc [[0, 3], [4, 5]],
    cyc [[0, 3, 1, 2], [4, 5]],
    cyc [[0, 3], [1, 2]]]

end CFSG.QuasithinUnique.Unc25G2.A7
