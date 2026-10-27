module

public import CFSG.GH74.GLS.C3.Layer2.L5C3a
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C3a

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose, macro_inline] def limp (a b : Bool) : Bool :=
  match a with
  | true => b
  | false => true

@[expose] def e16Chk (L R : List (Perm (Fin 16))) : Bool :=
  let L' := L.map nrm
  let R' := R.map nrm
  L'.all fun t => limp (decide (t ≠ 1 ∧ t * t = 1 ∧ t ∉ R'))
    (decide ((L'.filter fun u => decide (u ≠ 1 ∧ u * u = 1 ∧ t * u = u * t)).length < 15))

end CFSG.GH74.GLS.C3.Layer2.L5
