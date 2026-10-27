
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5bBase
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5bBase
public import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5C5a
public import CFSG.GH74.GLS.C3.Layer2.L5C0Base
public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem getD_lt_of_all {l : List Nat} (h : l.all (fun n => decide (n < 128)) = true) (k : Nat) :
    l.getD k 0 < 128 := by
  by_cases hk : k < l.length
  · rw [getD_of_lt hk]
    exact of_decide_eq_true ((List.all_eq_true.1 h) _ (List.getElem_mem hk))
  · rw [getD_of_ge (Nat.le_of_not_lt hk)]
    norm_num

end CFSG.GH74.GLS.C3.Layer2.L5
