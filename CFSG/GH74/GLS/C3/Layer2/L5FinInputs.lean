module

public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def imp (a b : Bool) : Bool := !a || b

@[expose] def vhat5 : Amb 5 := e1 * f1

@[expose] def E5list : List (Amb 5) :=
  [1, vhat5, f1, e1, (swap 0 1, swap 0 1), (swap 0 1, swap 2 3), (swap 2 3, swap 0 1),
    (swap 2 3, swap 2 3)]

@[expose] def F5list : List (Amb 5) :=
  allAmb5.filter fun g => decide (g.2 * x4 = x4 * g.2 ∧ sign g.1 = sign g.2)

@[expose] def R5list : List (Perm (Fin 9)) := allT5.map (emb 5)

@[expose] def yS : Perm (Fin 9) := emb 5 vhat5

@[expose] def E9l : List (Perm (Fin 9)) := E5list.map (emb 5)

@[expose] def Rc9list : List (Perm (Fin 9)) :=
  [1, emb 5 e2, emb 5 f2, emb 5 (e2 * f2), a0perm 5, emb 5 e2 * a0perm 5, emb 5 f2 * a0perm 5,
    emb 5 (e2 * f2) * a0perm 5]

end CFSG.GH74.GLS.C3.Layer2.L5
