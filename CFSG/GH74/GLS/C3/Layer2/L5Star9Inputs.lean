module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions
public import Mathlib.GroupTheory.Complement
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3
open scoped Pointwise
@[expose] def g1 : Perm (Fin 9) := swap 0 2 * swap 1 3

@[expose] def g2 : Perm (Fin 9) := swap 2 5 * swap 3 6

@[expose] def g3 : Perm (Fin 9) := swap 5 7 * swap 6 8

@[expose] def D3list : List (Perm (Fin 9)) :=
  [1, g1] ++ [1, g1].map (· * g2) ++ [1, g1].map (· * g2 * g1)

@[expose] def D9list : List (Perm (Fin 9)) :=
  D3list ++ D3list.map (· * g3) ++ D3list.map (· * g3 * g2) ++ D3list.map (· * g3 * g2 * g1)

end CFSG.GH74.GLS.C3.Layer2.L5
