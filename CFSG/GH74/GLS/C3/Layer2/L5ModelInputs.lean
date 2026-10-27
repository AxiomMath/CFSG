module

public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def V5list : List (Perm (Fin 5)) := [1, z5, y5, z5 * y5]

@[expose] def V4list : List (Perm (Fin 4)) := [1, x4, y4, x4 * y4]

@[expose] def Rlist5 : List (Amb 5) := V5list.flatMap fun σ => V4list.map fun d => (σ, d)

@[expose] def mk4 (g1 g2 g3 g4 : Amb 5) (a b c d : Bool) : Amb 5 :=
  cond a g1 1 * cond b g2 1 * cond c g3 1 * cond d g4 1

end CFSG.GH74.GLS.C3.Layer2.L5
