module

public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
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

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def el16 (i : Fin 16) : Amb 5 := Rml.getD i.val 1

@[expose] def idx16 (r : Amb 5) : Fin 16 :=
  ⟨Rml.findIdx (fun x => decide (x = r)) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def xor16 (a b : Fin 16) : Fin 16 :=
  ⟨a.val ^^^ b.val, by
    have := Nat.xor_lt_two_pow (n := 4) (x := a.val) (y := b.val)
      (by simp) (by simp)
    simpa using this⟩

@[expose] def tr16 (v : Fin 16) : Perm (Fin 16) where
  toFun i := xor16 i v
  invFun i := xor16 i v
  left_inv i := Fin.ext (by simp [xor16, Nat.xor_assoc])
  right_inv i := Fin.ext (by simp [xor16, Nat.xor_assoc])

@[expose] def yy5 : Amb 5 := (swap 2 3, swap 2 3)

@[expose] def actF (t : Amb 5) (i : Fin 16) : Fin 16 := idx16 (t * el16 i * t⁻¹)

@[expose] def yHat : Perm (Fin 16) := List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 12] * List.formPerm [9, 13] * List.formPerm [10, 15] * List.formPerm [11, 14]

@[expose] def wHat : Perm (Fin 16) := List.formPerm [4, 8, 12] * List.formPerm [5, 9, 13] * List.formPerm [6, 10, 14] * List.formPerm [7, 11, 15]

@[expose] def d8L : List (Perm (Fin 16)) :=
  [1,
    List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 12] * List.formPerm [9, 13] * List.formPerm [10, 15] * List.formPerm [11, 14],
    List.formPerm [1, 5] * List.formPerm [2, 11] * List.formPerm [3, 14] * List.formPerm [6, 15] * List.formPerm [7, 10] * List.formPerm [8, 12],
    List.formPerm [1, 5] * List.formPerm [2, 14] * List.formPerm [3, 11] * List.formPerm [6, 10] * List.formPerm [7, 15] * List.formPerm [9, 13],
    List.formPerm [1, 9] * List.formPerm [2, 6] * List.formPerm [3, 15] * List.formPerm [5, 13] * List.formPerm [7, 11] * List.formPerm [10, 14],
    List.formPerm [1, 9, 5, 13] * List.formPerm [2, 15, 14, 7] * List.formPerm [3, 6, 11, 10] * List.formPerm [8, 12],
    List.formPerm [1, 13, 5, 9] * List.formPerm [2, 7, 14, 15] * List.formPerm [3, 10, 11, 6] * List.formPerm [8, 12],
    List.formPerm [1, 13] * List.formPerm [2, 10] * List.formPerm [3, 7] * List.formPerm [5, 9] * List.formPerm [6, 14] * List.formPerm [11, 15]]

@[expose] def mulClosedChkP {M : Type*} [Mul M] [DecidableEq M] (l : List M) : Bool :=
  l.all fun a => l.all fun b => decide (a * b ∈ l)

@[expose] def invClosedChkP {M : Type*} [Group M] [DecidableEq M] (l : List M) : Bool :=
  l.all fun a => decide (a⁻¹ ∈ l)

@[expose] def Sh0L : List (Perm (Fin 16)) :=
  (List.finRange 16).flatMap fun v => d8L.map fun d => tr16 v * d

@[expose] def tr1L : List (Perm (Fin 16)) :=
  [1,
    List.formPerm [0, 3] * List.formPerm [1, 12] * List.formPerm [2, 8] * List.formPerm [4, 5] * List.formPerm [6, 10] * List.formPerm [7, 13] * List.formPerm [9, 14] * List.formPerm [11, 15],
    List.formPerm [0, 8] * List.formPerm [1, 9] * List.formPerm [2, 3] * List.formPerm [4, 6] * List.formPerm [5, 10] * List.formPerm [7, 11] * List.formPerm [12, 14] * List.formPerm [13, 15],
    List.formPerm [0, 2] * List.formPerm [1, 14] * List.formPerm [3, 8] * List.formPerm [4, 10] * List.formPerm [5, 6] * List.formPerm [7, 15] * List.formPerm [9, 12] * List.formPerm [11, 13],
    List.formPerm [0, 9] * List.formPerm [1, 8] * List.formPerm [2, 12] * List.formPerm [3, 14] * List.formPerm [4, 15] * List.formPerm [5, 11] * List.formPerm [6, 13] * List.formPerm [7, 10],
    List.formPerm [0, 14] * List.formPerm [1, 2] * List.formPerm [3, 9] * List.formPerm [4, 11] * List.formPerm [5, 15] * List.formPerm [6, 7] * List.formPerm [8, 12] * List.formPerm [10, 13],
    List.formPerm [0, 1] * List.formPerm [2, 14] * List.formPerm [3, 12] * List.formPerm [4, 13] * List.formPerm [5, 7] * List.formPerm [6, 15] * List.formPerm [8, 9] * List.formPerm [10, 11],
    List.formPerm [0, 12] * List.formPerm [1, 3] * List.formPerm [2, 9] * List.formPerm [4, 7] * List.formPerm [5, 13] * List.formPerm [6, 11] * List.formPerm [8, 14] * List.formPerm [10, 15],
    List.formPerm [4, 15] * List.formPerm [5, 11] * List.formPerm [6, 13] * List.formPerm [7, 10],
    List.formPerm [0, 3] * List.formPerm [1, 12] * List.formPerm [2, 8] * List.formPerm [4, 11] * List.formPerm [5, 15] * List.formPerm [6, 7] * List.formPerm [9, 14] * List.formPerm [10, 13],
    List.formPerm [0, 8] * List.formPerm [1, 9] * List.formPerm [2, 3] * List.formPerm [4, 13] * List.formPerm [5, 7] * List.formPerm [6, 15] * List.formPerm [10, 11] * List.formPerm [12, 14],
    List.formPerm [0, 2] * List.formPerm [1, 14] * List.formPerm [3, 8] * List.formPerm [4, 7] * List.formPerm [5, 13] * List.formPerm [6, 11] * List.formPerm [9, 12] * List.formPerm [10, 15],
    List.formPerm [0, 9] * List.formPerm [1, 8] * List.formPerm [2, 12] * List.formPerm [3, 14],
    List.formPerm [0, 14] * List.formPerm [1, 2] * List.formPerm [3, 9] * List.formPerm [4, 5] * List.formPerm [6, 10] * List.formPerm [7, 13] * List.formPerm [8, 12] * List.formPerm [11, 15],
    List.formPerm [0, 1] * List.formPerm [2, 14] * List.formPerm [3, 12] * List.formPerm [4, 6] * List.formPerm [5, 10] * List.formPerm [7, 11] * List.formPerm [8, 9] * List.formPerm [13, 15],
    List.formPerm [0, 12] * List.formPerm [1, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 6] * List.formPerm [7, 15] * List.formPerm [8, 14] * List.formPerm [11, 13]]

@[expose] def tr1 (v : Fin 16) : Perm (Fin 16) := tr1L.getD v.val 1

@[expose] def yHat1 : Perm (Fin 16) := List.formPerm [0, 15] * List.formPerm [1, 10] * List.formPerm [2, 13] * List.formPerm [3, 11] * List.formPerm [4, 9] * List.formPerm [5, 14] * List.formPerm [6, 12] * List.formPerm [7, 8]

@[expose] def xHat1 : Perm (Fin 16) := List.formPerm [0, 1, 9, 8] * List.formPerm [2, 3, 12, 14] * List.formPerm [4, 5, 15, 11] * List.formPerm [6, 7, 13, 10]

@[expose] def sh1Gens : List (Perm (Fin 16)) := [tr1 1, tr1 2, tr1 4, tr1 8, yHat1, xHat1]

@[expose] def Sh1L : List (Perm (Fin 16)) := closureList sh1Gens 12

@[expose] def emb48 (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16)) (t : Amb 5) :
    Perm (Fin 16) :=
  if t ∈ Rml then Tr (idx16 t) else Tr (idx16 (t * yy5)) * yy

@[expose] def v4L : List (Perm (Fin 16)) := [d8L.getD 0 1, d8L.getD 3 1, d8L.getD 4 1, d8L.getD 7 1]

@[expose] def rhoF (Tr : Fin 16 → Perm (Fin 16)) (s : Perm (Fin 16)) (i : Fin 16) : Fin 16 :=
  ((List.finRange 16).find? fun j => decide (s * Tr i * s⁻¹ = Tr j)).getD 0

@[expose] def overV4 (Tr : Fin 16 → Perm (Fin 16)) (s : Perm (Fin 16)) : Bool :=
  v4L.any fun d => (List.finRange 16).all fun i => decide (d i = rhoF Tr s i)

@[expose] def S0L0 : List (Perm (Fin 16)) := Sh0L.filter (overV4 tr16)

@[expose] def S0L1 : List (Perm (Fin 16)) := Sh1L.filter (overV4 tr1)

@[expose] def R1L : List (Perm (Fin 16)) :=
  [1,
    List.formPerm [1, 5] * List.formPerm [2, 14] * List.formPerm [3, 11] * List.formPerm [6, 10] * List.formPerm [7, 15] * List.formPerm [9, 13],
    List.formPerm [1, 9] * List.formPerm [2, 6] * List.formPerm [3, 15] * List.formPerm [5, 13] * List.formPerm [7, 11] * List.formPerm [10, 14],
    List.formPerm [1, 13] * List.formPerm [2, 10] * List.formPerm [3, 7] * List.formPerm [5, 9] * List.formPerm [6, 14] * List.formPerm [11, 15],
    List.formPerm [0, 4] * List.formPerm [2, 10] * List.formPerm [3, 15] * List.formPerm [6, 14] * List.formPerm [7, 11] * List.formPerm [8, 12],
    List.formPerm [0, 4] * List.formPerm [1, 5] * List.formPerm [2, 6] * List.formPerm [3, 7] * List.formPerm [8, 12] * List.formPerm [9, 13] * List.formPerm [10, 14] * List.formPerm [11, 15],
    List.formPerm [0, 4] * List.formPerm [1, 9] * List.formPerm [2, 14] * List.formPerm [5, 13] * List.formPerm [6, 10] * List.formPerm [8, 12],
    List.formPerm [0, 4] * List.formPerm [1, 13] * List.formPerm [3, 11] * List.formPerm [5, 9] * List.formPerm [7, 15] * List.formPerm [8, 12],
    List.formPerm [0, 8] * List.formPerm [2, 14] * List.formPerm [3, 7] * List.formPerm [4, 12] * List.formPerm [6, 10] * List.formPerm [11, 15],
    List.formPerm [0, 8] * List.formPerm [1, 5] * List.formPerm [3, 15] * List.formPerm [4, 12] * List.formPerm [7, 11] * List.formPerm [9, 13],
    List.formPerm [0, 8] * List.formPerm [1, 9] * List.formPerm [2, 10] * List.formPerm [3, 11] * List.formPerm [4, 12] * List.formPerm [5, 13] * List.formPerm [6, 14] * List.formPerm [7, 15],
    List.formPerm [0, 8] * List.formPerm [1, 13] * List.formPerm [2, 6] * List.formPerm [4, 12] * List.formPerm [5, 9] * List.formPerm [10, 14],
    List.formPerm [0, 12] * List.formPerm [2, 6] * List.formPerm [3, 11] * List.formPerm [4, 8] * List.formPerm [7, 15] * List.formPerm [10, 14],
    List.formPerm [0, 12] * List.formPerm [1, 5] * List.formPerm [2, 10] * List.formPerm [4, 8] * List.formPerm [6, 14] * List.formPerm [9, 13],
    List.formPerm [0, 12] * List.formPerm [1, 9] * List.formPerm [3, 7] * List.formPerm [4, 8] * List.formPerm [5, 13] * List.formPerm [11, 15],
    List.formPerm [0, 12] * List.formPerm [1, 13] * List.formPerm [2, 14] * List.formPerm [3, 15] * List.formPerm [4, 8] * List.formPerm [5, 9] * List.formPerm [6, 10] * List.formPerm [7, 11]]

@[expose] def RhatL0 : List (Perm (Fin 16)) := (List.finRange 16).map tr16

@[expose] def RhatL1 : List (Perm (Fin 16)) := (List.finRange 16).map tr1

end CFSG.GH74.GLS.C3.Layer2.L5
