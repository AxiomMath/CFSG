module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def z5 : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def y5 : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def y4 : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def T5b (p : Amb 5) : Bool :=
  decide (p.2 * x4 = x4 * p.2 ∧ sign p.1 = sign p.2 ∧ p.1 * z5 = z5 * p.1)

@[expose] def g5Perms : (m : ℕ) → List (Perm (Fin m))
  | 0 => [1]
  | m + 1 => (List.finRange (m + 1)).flatMap fun p =>
      (g5Perms m).map fun e => Equiv.Perm.decomposeFin.symm (p, e)

@[expose] def allAmb5 : List (Amb 5) :=
  (g5Perms 5).flatMap fun σ => (g5Perms 4).map fun d => (σ, d)

@[expose] def allT5 : List (Amb 5) := allAmb5.filter T5b

@[expose] def e1 : Amb 5 := (z5, 1)

@[expose] def e2 : Amb 5 := (y5, 1)

@[expose] def f1 : Amb 5 := x0 5

@[expose] def f2 : Amb 5 := (1, y4)

@[expose] def nmE (p : Amb 5) : ℕ := numMoved (emb 5 p)

@[expose] def W1P (u₁ w : Amb 5) : Prop :=
  (nmE u₁ = nmE w ∧ nmE (u₁ * f1) = nmE (w * f1) ∧ nmE u₁ = nmE (u₁ * w)) →
    (u₁ = e1 ∧ (w = e2 ∨ w = e1 * e2))

@[expose] def U1P (w u : Amb 5) : Prop :=
  (u ≠ 1 ∧ u ≠ f1 ∧ nmE u = 4 ∧ nmE (f1 * u) = 4 ∧ u * w = w * u) → (u = f2 ∨ u = f1 * f2)

end CFSG.GH74.GLS.C3.Prop121
