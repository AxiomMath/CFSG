module

public import Mathlib.GroupTheory.Perm.Sign
public import Certificates.Data.CFSGNative.Mathieu.M11
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Holt.SmallGroups

open Equiv

@[expose] def s7Words : List (List (Fin 3)) :=
  [ [1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2],
    [0, 2, 0, 2, 0, 2], [0, 0, 2, 0, 0, 2, 0, 0, 2], [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2],
    [0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 2, 1], [1, 2, 1, 2, 1, 2],
    [0, 0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 2], [0, 0, 0, 0, 2, 0, 0, 2, 0, 2],
    [0, 0, 0, 0, 2, 0, 2, 0, 0, 2], [0, 2, 0, 2, 0, 2, 0, 2, 0, 2], [0, 2, 1, 0, 2, 1, 0, 2, 1],
    [0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 2], [0, 0, 0, 0, 0, 1, 0, 2],
    [0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 0, 1, 0, 1], [0, 0, 2, 0, 1, 2, 1, 0, 2],
    [0, 0, 0, 2, 1, 0, 2, 0, 2], [0, 0, 0, 2, 0, 2, 1, 0, 2], [0, 1, 2, 0, 1, 2, 1, 0, 2, 1],
    [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 1], [0, 0, 0, 1, 2], [0, 0, 1, 0, 0, 1, 2],
    [0, 2, 1, 0, 2, 1, 2, 1], [0, 0, 1, 2, 0, 2, 1, 0, 2], [0, 0, 0, 0, 1, 0, 0, 0, 2],
    [0, 0, 1, 2, 0, 2, 1, 2, 1], [0, 0, 2, 1, 2, 1, 0, 1, 2], [0, 0, 0, 0, 2, 0, 0, 0, 1],
    [0, 0, 1, 0, 2, 0, 0, 2, 1, 2], [0, 0, 2, 0, 1, 0, 0, 2, 1, 2],
    [0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 1], [0, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1],
    [0, 0, 1, 2, 0, 1, 2, 1, 0, 1, 2], [0, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2],
    [0, 2, 1, 2, 1, 0, 2, 1, 2, 1, 2, 1], [0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 2, 1],
    [0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 2], [0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 0, 1, 2, 0, 1, 0, 0, 1, 0, 1],
    [0, 0, 1, 0, 1, 2, 0, 1, 0, 0, 1, 2, 0, 0, 1, 2] ]

@[expose] def s7Gen (u t : Perm (Fin 7)) : Fin 3 → Perm (Fin 7)
  | 0 => finRotate 7
  | 1 => u
  | 2 => t

@[expose] def s7Eval (u t : Perm (Fin 7)) (w : List (Fin 3)) : Perm (Fin 7) :=
  w.foldl (fun x k => s7Gen u t k * x) 1

@[expose] def s7U : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun u => u * u = 1 ∧ (Finset.univ.filter fun x => u x = x).card = 3

@[expose] def s7T : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun t => t * t = 1 ∧ ∀ x, t x = x ↔ x = 0

@[expose] def m11Data4 : CFSG.Sporadic.Mathieu.Native.Data :=
  { CFSG.Sporadic.Mathieu.Native.m11Data with k := 4 }

@[expose] def a7Involutions : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun σ => σ * σ = 1 ∧ σ ≠ 1 ∧ Perm.sign σ = 1

end CFSG.Holt.SmallGroups
