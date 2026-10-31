
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
public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem getD_of_lt {α : Type*} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_of_ge {α : Type*} {l : List α} {i : Nat} {d : α} (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

def evFrom (x : List Nat) (a : Nat) (w : List Nat) : Nat :=
  w.foldl (fun a k => mt0.getD (a * 128 + x.getD k 0) 0) a

def evI (x : List Nat) (w : List Nat) : Nat := evFrom x 0 w

def evH {H : Type*} [Monoid H] (f : Nat → H) (w : List Nat) : H :=
  w.foldl (fun A k => A * f k) 1

theorem foldl_map_hom {H H' : Type*} [Monoid H] [Monoid H'] (f : H →* H') (g : Nat → H)
    (w : List Nat) (A : H) :
    f (w.foldl (fun A k => A * g k) A) = w.foldl (fun B k => B * f (g k)) (f A) := by
  induction w generalizing A with
  | nil => rfl
  | cons k w ih =>
    simp only [List.foldl_cons]
    rw [ih, map_mul]

theorem evH_map {H H' : Type*} [Monoid H] [Monoid H'] (f : H →* H') (g : Nat → H)
    (w : List Nat) : f (evH g w) = evH (fun k => f (g k)) w := by
  unfold evH
  rw [foldl_map_hom, map_one]

end CFSG.GH74.GLS.C3.Layer2.L5
