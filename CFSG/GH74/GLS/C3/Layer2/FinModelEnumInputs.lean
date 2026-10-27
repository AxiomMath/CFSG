module

public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import Mathlib.Data.List.Dedup
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup
@[expose] def closureStep {G : Type*} [Mul G] [DecidableEq G] (gens : List G) (l : List G) :
    List G :=
  (l ++ l.flatMap fun g => gens.map (g * ·)).dedup

@[expose] def closureList {G : Type*} [Mul G] [One G] [DecidableEq G] (gens : List G) (k : ℕ) :
    List G :=
  (closureStep gens)^[k] [1]

@[expose] def sigmaGensList (n : ℕ) [NeZero n] : List (Perm (Fin n)) :=
  [swap 0 1, swap 2 3, swap 0 2 * swap 1 3, swap 4 5]

@[expose] def Pl (n : ℕ) [NeZero n] : List (Perm (Fin n)) := closureList (sigmaGensList n) 8

@[expose] def dGensList : List (Perm (Fin 4)) := [swap 0 1, swap 2 3, swap 0 2 * swap 1 3]

@[expose] def Dl : List (Perm (Fin 4)) := closureList dGensList 8

@[expose] def Tl (n : ℕ) [NeZero n] : List (Amb n) :=
  (Pl n).flatMap fun σ => (Dl.filter fun d => sign σ = sign d).map fun d => (σ, d)

@[expose] def plClosedB (n : ℕ) [NeZero n] : Bool :=
  (Pl n).all (fun a => (Pl n).all fun b => decide (a * b ∈ Pl n)) &&
    (Pl n).all (fun a => decide (a⁻¹ ∈ Pl n)) &&
    (sigmaGensList n).all (fun a => decide (a ∈ Pl n))

@[expose] def tlFactsB (n : ℕ) [NeZero n] : Bool :=
  decide ((Tl n).length = 64) && decide ((Tl n).Nodup) && decide ((Pl n).length = 16)

end CFSG.GH74.GLS.C3.Layer2.Model
