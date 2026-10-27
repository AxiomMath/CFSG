module

public import CFSG.GH74.GLS.C3.Layer2.L5C4a
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4a

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
@[expose] def tau1L : List (Perm (Fin 16)) :=
  [1,
    List.formPerm [0, 6, 14, 7] * List.formPerm [1, 11, 2, 4] * List.formPerm [3, 10, 9, 13] * List.formPerm [5, 12, 15, 8],
    List.formPerm [0, 5, 14, 4] * List.formPerm [1, 6, 2, 10] * List.formPerm [3, 15, 9, 11] * List.formPerm [7, 8, 13, 12],
    List.formPerm [0, 14, 9, 3] * List.formPerm [1, 12, 8, 2] * List.formPerm [5, 11] * List.formPerm [7, 10],
    List.formPerm [1, 8] * List.formPerm [2, 12] * List.formPerm [4, 10] * List.formPerm [5, 13] * List.formPerm [6, 11] * List.formPerm [7, 15],
    List.formPerm [0, 13, 1, 5, 9, 6, 8, 11] * List.formPerm [2, 4, 14, 7, 12, 15, 3, 10],
    List.formPerm [0, 10, 2, 11] * List.formPerm [1, 4, 3, 6] * List.formPerm [5, 9, 7, 12] * List.formPerm [8, 15, 14, 13],
    List.formPerm [0, 3, 9, 14] * List.formPerm [1, 12, 8, 2] * List.formPerm [4, 7, 15, 10] * List.formPerm [5, 13, 11, 6]]

@[expose] def tau1 (k : Fin 8) : Perm (Fin 16) := tau1L.getD k.val 1

@[expose] def cc1 (j k : Fin 8) : Fin 16 :=
  ((List.finRange 16).find? fun v =>
    decide (tau1 j * tau1 k = tr1 v * tau1 (mulIdx j k))).getD 0

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1
