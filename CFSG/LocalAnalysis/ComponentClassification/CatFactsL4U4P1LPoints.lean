module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open Matrix

abbrev V : Type := Fin 4 → ZMod 3

@[expose] def lead (v : V) : ZMod 3 :=
  if v 0 ≠ 0 then v 0 else if v 1 ≠ 0 then v 1 else if v 2 ≠ 0 then v 2 else v 3

@[expose] def normalize (v : V) : V := lead v • v

@[expose] def rawIndex (v : V) : ℕ :=
  if v 0 ≠ 0 then 9 * (v 1).val + 3 * (v 2).val + (v 3).val
  else if v 1 ≠ 0 then 27 + 3 * (v 2).val + (v 3).val
  else if v 2 ≠ 0 then 36 + (v 3).val else 39

@[expose] def ptIndex (v : V) : ℕ := rawIndex (normalize v)

@[expose] def decode (i : ℕ) : V :=
  if i < 27 then ![1, ((i / 9 : ℕ) : ZMod 3), ((i / 3 % 3 : ℕ) : ZMod 3), ((i % 3 : ℕ) : ZMod 3)]
  else if i < 36 then ![0, 1, (((i - 27) / 3 : ℕ) : ZMod 3), (((i - 27) % 3 : ℕ) : ZMod 3)]
  else if i < 39 then ![0, 0, 1, ((i - 36 : ℕ) : ZMod 3)] else ![0, 0, 0, 1]

theorem ptIndex_decode : ∀ i : Fin 40, ptIndex (decode i) = i := by
  decide +kernel

@[expose] def mv4 (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : V) : V :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 + A i 3 * v 3

@[expose] def matN (k : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => ((k / 3 ^ (4 * i.val + j.val) : ℕ) : ZMod 3)

@[expose] def ptTab (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Array ℕ :=
  Array.ofFn (n := 40) fun i => ptIndex (mv4 A (decode i.val))

@[expose] def invTab40 (t : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 40) fun j => ((List.range 40).find? fun i => t[i]! == j.val).getD 0

@[expose] def swapTab : Array ℕ := Array.ofFn (n := 80) fun i => if i.val < 40 then i.val + 40
  else i.val - 40

@[expose] def tabA80 (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Array ℕ :=
  ptTab A ++ (invTab40 (ptTab Aᵀ)).map (· + 40)

@[expose] def tab80 (k : ℕ) (ε : Bool) : Array ℕ :=
  let t := tabA80 (matN k)
  if ε then Array.ofFn (n := 80) fun i => t[swapTab[i.val]!]! else t

end CFSG.ComponentClassification.HarrisLit.P1.L43
