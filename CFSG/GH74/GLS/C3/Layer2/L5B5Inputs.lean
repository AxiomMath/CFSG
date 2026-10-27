module

public import CFSG.GH74.GLS.C3.Layer2.L5B0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def mixb (z : Amb 5) : Bool := decide (z ∈ Rml) && !decide (z ∈ Pml) && !decide (z ∈ Qml)

@[expose] def ZTl : List (Amb 5) := [1, e1, f1, e1 * f1]

end CFSG.GH74.GLS.C3.Layer2.L5
