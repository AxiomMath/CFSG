module

public import CFSG.GH74.GLS.C3.Layer2.L5C0
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

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def Dg (k : Fin 8) : Perm (Fin 16) := d8L.getD k.val 1

@[expose] def mulIdx (j k : Fin 8) : Fin 8 :=
  ⟨(d8L.findIdx fun d => decide (d = Dg j * Dg k)) % 8, Nat.mod_lt _ (by norm_num)⟩

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1
