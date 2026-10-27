
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5a
public import CFSG.GH74.GLS.C3.Layer2.L5C0Base
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0Base

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def pcode (p : Perm (Fin 16)) : Nat :=
  (List.finRange 16).foldl (fun acc i => acc * 16 + (p i).val) 0

@[expose] def sh0Codes : List Nat := Sh0L.map pcode

@[expose] def sh0Idx (p : Perm (Fin 16)) : Nat := sh0Codes.idxOf (pcode p)

@[expose, irreducible] def mt0 : Array Nat :=
  let arr := Sh0L.toArray
  ((List.range 128).flatMap fun a => (List.range 128).map fun b =>
    sh0Idx (arr.getD a 1 * arr.getD b 1)).toArray

@[expose, irreducible] def inv0 : Array Nat := (Sh0L.map fun p => sh0Idx p⁻¹).toArray

@[expose] def mt0Chk : Bool :=
  (List.range 128).all fun a => (List.range 128).all fun b =>
    decide (mt0.getD (a * 128 + b) 0 < 128) &&
      decide (Sh0L.getD (mt0.getD (a * 128 + b) 0) 1 = Sh0L.getD a 1 * Sh0L.getD b 1)

@[expose] def inv0Chk : Bool :=
  (List.range 128).all fun a => decide (inv0.getD a 0 < 128) &&
    decide (Sh0L.getD (inv0.getD a 0) 1 = (Sh0L.getD a 1)⁻¹)

@[expose] def idx0 (p : Perm (Fin 16)) : Nat :=
  8 * (p 0).val + d8L.idxOf (tr16 (p 0) * p)

@[expose] def idx0Chk : Bool :=
  (List.range 128).all fun i => decide (idx0 (Sh0L.getD i 1) = i)

end CFSG.GH74.GLS.C3.Layer2.L5
