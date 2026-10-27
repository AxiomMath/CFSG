module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix
@[expose] def pa : Equiv.Perm (Fin 21) :=
  List.formPerm [0, 7] * List.formPerm [2, 19] * List.formPerm [3, 15] * List.formPerm [4, 11] * List.formPerm [5, 8] * List.formPerm [9, 16] * List.formPerm [12, 17] * List.formPerm [13, 20]

@[expose] def pb : Equiv.Perm (Fin 21) :=
  List.formPerm [0, 5, 12, 16] * List.formPerm [1, 13, 7, 4] * List.formPerm [2, 17] * List.formPerm [3, 9, 18, 10] * List.formPerm [6, 19, 20, 15] * List.formPerm [8, 14]

@[expose] def pa' : Equiv.Perm (Fin 21) :=
  List.formPerm [0, 7] * List.formPerm [2, 19] * List.formPerm [3, 15] * List.formPerm [4, 11] * List.formPerm [5, 8] * List.formPerm [9, 16] * List.formPerm [12, 17] * List.formPerm [13, 20]

@[expose] def pb' : Equiv.Perm (Fin 21) :=
  List.formPerm [0, 20, 16, 5] * List.formPerm [1, 3, 7, 17] * List.formPerm [2, 14, 10, 13] * List.formPerm [4, 9] * List.formPerm [6, 19, 12, 11] * List.formPerm [8, 18]

@[expose] def PA : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 7] * List.formPerm [2, 19] * List.formPerm [3, 15] * List.formPerm [4, 11] * List.formPerm [5, 8] * List.formPerm [9, 16] * List.formPerm [12, 17] * List.formPerm [13, 20] * List.formPerm [21, 28] * List.formPerm [23, 40] * List.formPerm [24, 36] * List.formPerm [25, 32] * List.formPerm [26, 29] * List.formPerm [30, 37] * List.formPerm [33, 38] * List.formPerm [34, 41]

@[expose] def PB : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 5, 12, 16] * List.formPerm [1, 13, 7, 4] * List.formPerm [2, 17] * List.formPerm [3, 9, 18, 10] * List.formPerm [6, 19, 20, 15] * List.formPerm [8, 14] * List.formPerm [21, 41, 37, 26] * List.formPerm [22, 24, 28, 38] * List.formPerm [23, 35, 31, 34] * List.formPerm [25, 30] * List.formPerm [27, 40, 33, 32] * List.formPerm [29, 39]

@[expose] def QP21 : RawSchreierDatum 21 :=
  certificate (by decide) [pa, pb] [[-2, -1, -2, -2, 1, 2], [-1, 3, 1], [-2, 3, 2], [-3, 5, 3], [-4, 6, 4], [-5, -7, 6, 4, 5], [-3, -4, -8, -3, -2, 8, 1], [-6, 9, 6]] #v[0, 1, 5, 2] (by decide)

@[expose] def QP : RawSchreierDatum 42 :=
  certificate (by decide) [PA, PB] [[-2, -1, -2, -2, 1, 2], [-1, 3, 1], [-2, 3, 2], [-3, 5, 3], [-4, 6, 4], [-5, -7, 6, 4, 5], [-3, -4, -8, -3, -2, 8, 1], [-6, 9, 6]] #v[0, 1, 5, 2] (by decide)

end CFSG.GH74.KGroups.L34
