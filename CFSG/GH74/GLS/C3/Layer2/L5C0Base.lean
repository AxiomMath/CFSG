
module

public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
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
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def n24L : List (Perm (Fin 16)) :=
  [1,
    List.formPerm [4, 8, 12] * List.formPerm [5, 9, 13] * List.formPerm [6, 10, 14] * List.formPerm [7, 11, 15],
    List.formPerm [4, 12, 8] * List.formPerm [5, 13, 9] * List.formPerm [6, 14, 10] * List.formPerm [7, 15, 11],
    List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 12] * List.formPerm [9, 13] * List.formPerm [10, 15] * List.formPerm [11, 14],
    List.formPerm [2, 3] * List.formPerm [4, 8] * List.formPerm [5, 9] * List.formPerm [6, 11] * List.formPerm [7, 10] * List.formPerm [14, 15],
    List.formPerm [2, 3] * List.formPerm [4, 12] * List.formPerm [5, 13] * List.formPerm [6, 15] * List.formPerm [7, 14] * List.formPerm [10, 11],
    List.formPerm [1, 5] * List.formPerm [2, 11] * List.formPerm [3, 14] * List.formPerm [6, 15] * List.formPerm [7, 10] * List.formPerm [8, 12],
    List.formPerm [1, 5, 13, 9] * List.formPerm [2, 11, 10, 15] * List.formPerm [3, 14, 7, 6] * List.formPerm [4, 8],
    List.formPerm [1, 5, 9, 13] * List.formPerm [2, 11, 6, 7] * List.formPerm [3, 14, 15, 10] * List.formPerm [4, 12],
    List.formPerm [1, 5] * List.formPerm [2, 14] * List.formPerm [3, 11] * List.formPerm [6, 10] * List.formPerm [7, 15] * List.formPerm [9, 13],
    List.formPerm [1, 5, 13] * List.formPerm [2, 14, 10] * List.formPerm [3, 11, 7] * List.formPerm [4, 8, 12],
    List.formPerm [1, 5, 9] * List.formPerm [2, 14, 6] * List.formPerm [3, 11, 15] * List.formPerm [4, 12, 8],
    List.formPerm [1, 9] * List.formPerm [2, 6] * List.formPerm [3, 15] * List.formPerm [5, 13] * List.formPerm [7, 11] * List.formPerm [10, 14],
    List.formPerm [1, 9, 5] * List.formPerm [2, 6, 14] * List.formPerm [3, 15, 11] * List.formPerm [4, 8, 12],
    List.formPerm [1, 9, 13] * List.formPerm [2, 6, 10] * List.formPerm [3, 15, 7] * List.formPerm [4, 12, 8],
    List.formPerm [1, 9, 5, 13] * List.formPerm [2, 15, 14, 7] * List.formPerm [3, 6, 11, 10] * List.formPerm [8, 12],
    List.formPerm [1, 9, 13, 5] * List.formPerm [2, 15, 10, 11] * List.formPerm [3, 6, 7, 14] * List.formPerm [4, 8],
    List.formPerm [1, 9] * List.formPerm [2, 15] * List.formPerm [3, 6] * List.formPerm [4, 12] * List.formPerm [7, 10] * List.formPerm [11, 14],
    List.formPerm [1, 13, 5, 9] * List.formPerm [2, 7, 14, 15] * List.formPerm [3, 10, 11, 6] * List.formPerm [8, 12],
    List.formPerm [1, 13] * List.formPerm [2, 7] * List.formPerm [3, 10] * List.formPerm [4, 8] * List.formPerm [6, 15] * List.formPerm [11, 14],
    List.formPerm [1, 13, 9, 5] * List.formPerm [2, 7, 6, 11] * List.formPerm [3, 10, 15, 14] * List.formPerm [4, 12],
    List.formPerm [1, 13] * List.formPerm [2, 10] * List.formPerm [3, 7] * List.formPerm [5, 9] * List.formPerm [6, 14] * List.formPerm [11, 15],
    List.formPerm [1, 13, 9] * List.formPerm [2, 10, 6] * List.formPerm [3, 7, 15] * List.formPerm [4, 8, 12],
    List.formPerm [1, 13, 5] * List.formPerm [2, 10, 14] * List.formPerm [3, 7, 11] * List.formPerm [4, 12, 8]]

theorem one_mem_Sh1L : (1 : Perm (Fin 16)) ∈ Sh1L := one_mem_closureList _ _

@[expose] def cHat : Perm (Fin 16) :=
  List.formPerm [1, 2, 3] * List.formPerm [5, 6, 7] * List.formPerm [9, 10, 11] *
    List.formPerm [13, 14, 15]

@[expose] def lsubP (l : List (Perm (Fin 16))) (h1 : (1 : Perm (Fin 16)) ∈ l)
    (hm : mulClosedChkP l = true) (hi : invClosedChkP l = true) : Subgroup (Perm (Fin 16)) :=
  lsub l h1 (by simpa only [mulClosedChkP, List.all_eq_true, decide_eq_true_eq] using hm)
    (by simpa only [invClosedChkP, List.all_eq_true, decide_eq_true_eq] using hi)

end CFSG.GH74.GLS.C3.Layer2.L5
