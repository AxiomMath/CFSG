module

public import Mathlib.GroupTheory.Perm.List

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv

@[expose] def PplG : Finset (Fin 16) := {0, 4, 8, 12}

@[expose] def QplG : Finset (Fin 16) := {0, 1, 2, 3}

@[expose] def fam0G : Finset (Finset (Fin 16)) :=
  {{0, 5, 11, 14}, {0, 7, 10, 13}, {0, 1, 2, 3}, {0, 6, 9, 15}}

@[expose] def fam1G : Finset (Finset (Fin 16)) :=
  {{0, 6, 11, 13}, {0, 7, 9, 14}, {0, 5, 10, 15}, {0, 1, 2, 3}}

@[expose] def twG : Perm (Fin 16) :=
  List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [10, 11] * List.formPerm [14, 15]

end CFSG.GH74.GLS.C3.Layer2.L5
