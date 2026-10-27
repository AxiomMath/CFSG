module

public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.LieType.ChevTwo.GL4Native

@[expose] def ij (k : Fin 16) : Fin 4 × Fin 4 := (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩)

@[expose] def ent (a : List (ZMod 2)) (i j : ℕ) : ZMod 2 := a.getD (4 * i + j) 0

@[expose] def mulL (a b : List (ZMod 2)) : List (ZMod 2) :=
  List.ofFn fun k : Fin 16 =>
    ent a (k.val / 4) 0 * ent b 0 (k.val % 4) + ent a (k.val / 4) 1 * ent b 1 (k.val % 4) +
    ent a (k.val / 4) 2 * ent b 2 (k.val % 4) + ent a (k.val / 4) 3 * ent b 3 (k.val % 4)

@[expose] def oneL : List (ZMod 2) := List.ofFn fun k : Fin 16 => if (ij k).1 = (ij k).2 then 1 else 0

@[expose] def trL (a : List (ZMod 2)) : ZMod 2 := ent a 0 0 + ent a 1 1 + ent a 2 2 + ent a 3 3

@[expose] def powL (a : List (ZMod 2)) (n : ℕ) : List (ZMod 2) :=
  if h : n = 0 then oneL
  else
    let p := powL a (n / 2)
    let s := mulL p p
    if n % 2 = 1 then mulL s a else s
termination_by n
decreasing_by omega

@[expose] def chk (a : List (ZMod 2)) : Bool :=
  !(decide (powL a 315 = oneL)) || decide (a = oneL) || decide (powL a 3 = oneL) ||
    decide (powL a 5 = oneL) || decide (trL a ≠ trL (powL a 314))

end CFSG.LieType.ChevTwo.GL4Native
