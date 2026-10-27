module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def mulClosedChk (l : List (Amb 5)) : Bool :=
  l.all fun a => l.all fun b => decide (a * b ∈ l)

@[expose] def invClosedChk (l : List (Amb 5)) : Bool := l.all fun a => decide (a⁻¹ ∈ l)

@[expose] def Pml : List (Amb 5) := [1, e1, e2, e1 * e2]

@[expose] def Qml : List (Amb 5) := [1, f1, f2, f1 * f2]

@[expose] def Rml : List (Amb 5) := Pml.flatMap fun p => Qml.map (p * ·)

@[expose] def Km : Subgroup (Amb 5) := (alternatingGroup (Fin 5)).map (MonoidHom.inl _ _)

@[expose] def wm : Amb 5 := (swap 1 2 * swap 2 3, 1)

@[expose] def V4l : List (Perm (Fin 4)) := [1, x4, y4, x4 * y4]

end CFSG.GH74.GLS.C3.Layer2.L5
