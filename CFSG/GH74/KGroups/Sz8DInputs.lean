module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic10
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Sz8
public import CFSG.GH74.KGroups.Sz8Tables
public import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Sz8
public meta import CFSG.GH74.KGroups.Sz8Tables
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Generic10

public section

namespace CFSG.GH74.KGroups.Sz8D

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8
@[expose] def xA : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 61, 14, 41] * List.formPerm [1, 30, 45, 31] * List.formPerm [2, 34, 38, 27] * List.formPerm [3, 21, 35, 43] * List.formPerm [4, 22, 7, 40] * List.formPerm [5, 64, 12, 56] * List.formPerm [6, 15, 53, 23] * List.formPerm [8, 10, 47, 33] * List.formPerm [9, 39, 32, 17] * List.formPerm [11, 36, 60, 29] * List.formPerm [13, 24, 51, 18] * List.formPerm [16, 57, 42, 46] * List.formPerm [19, 63, 62, 25] * List.formPerm [20, 54, 59, 44] * List.formPerm [26, 58, 49, 52] * List.formPerm [28, 48, 50, 55]

@[expose] def xB : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 21, 59, 31] * List.formPerm [1, 33, 35, 52] * List.formPerm [2, 40, 6, 11] * List.formPerm [3, 58, 45, 10] * List.formPerm [4, 13, 36, 28] * List.formPerm [5, 24, 62, 48] * List.formPerm [7, 51, 29, 50] * List.formPerm [8, 57, 26, 39] * List.formPerm [9, 61, 16, 44] * List.formPerm [12, 18, 19, 55] * List.formPerm [14, 43, 20, 30] * List.formPerm [15, 63, 34, 56] * List.formPerm [17, 47, 46, 49] * List.formPerm [22, 53, 60, 38] * List.formPerm [23, 25, 27, 64] * List.formPerm [32, 41, 42, 54]

@[expose] def xC : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 18, 47, 6] * List.formPerm [1, 7, 9, 64] * List.formPerm [2, 59, 55, 49] * List.formPerm [3, 36, 42, 63] * List.formPerm [4, 32, 56, 45] * List.formPerm [5, 46, 22, 21] * List.formPerm [8, 53, 14, 24] * List.formPerm [10, 50, 41, 27] * List.formPerm [11, 30, 19, 39] * List.formPerm [12, 57, 40, 43] * List.formPerm [13, 44, 15, 52] * List.formPerm [16, 25, 35, 29] * List.formPerm [17, 60, 31, 62] * List.formPerm [20, 48, 26, 38] * List.formPerm [23, 58, 51, 54] * List.formPerm [28, 61, 34, 33]

@[expose] def yA : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 59] * List.formPerm [1, 35] * List.formPerm [2, 6] * List.formPerm [3, 45] * List.formPerm [4, 36] * List.formPerm [5, 62] * List.formPerm [7, 29] * List.formPerm [8, 26] * List.formPerm [9, 16] * List.formPerm [10, 58] * List.formPerm [11, 40] * List.formPerm [12, 19] * List.formPerm [13, 28] * List.formPerm [14, 20] * List.formPerm [15, 34] * List.formPerm [17, 46] * List.formPerm [18, 55] * List.formPerm [21, 31] * List.formPerm [22, 60] * List.formPerm [23, 27] * List.formPerm [24, 48] * List.formPerm [25, 64] * List.formPerm [30, 43] * List.formPerm [32, 42] * List.formPerm [33, 52] * List.formPerm [38, 53] * List.formPerm [39, 57] * List.formPerm [41, 54] * List.formPerm [44, 61] * List.formPerm [47, 49] * List.formPerm [50, 51] * List.formPerm [56, 63]

@[expose] def yB : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 20] * List.formPerm [1, 3] * List.formPerm [2, 53] * List.formPerm [4, 29] * List.formPerm [5, 19] * List.formPerm [6, 38] * List.formPerm [7, 36] * List.formPerm [8, 49] * List.formPerm [9, 42] * List.formPerm [10, 52] * List.formPerm [11, 22] * List.formPerm [12, 62] * List.formPerm [13, 50] * List.formPerm [14, 59] * List.formPerm [15, 27] * List.formPerm [16, 32] * List.formPerm [17, 57] * List.formPerm [18, 48] * List.formPerm [21, 30] * List.formPerm [23, 34] * List.formPerm [24, 55] * List.formPerm [25, 56] * List.formPerm [26, 47] * List.formPerm [28, 51] * List.formPerm [31, 43] * List.formPerm [33, 58] * List.formPerm [35, 45] * List.formPerm [39, 46] * List.formPerm [40, 60] * List.formPerm [41, 44] * List.formPerm [54, 61] * List.formPerm [63, 64]

@[expose] def yC : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 47] * List.formPerm [1, 9] * List.formPerm [2, 55] * List.formPerm [3, 42] * List.formPerm [4, 56] * List.formPerm [5, 22] * List.formPerm [6, 18] * List.formPerm [7, 64] * List.formPerm [8, 14] * List.formPerm [10, 41] * List.formPerm [11, 19] * List.formPerm [12, 40] * List.formPerm [13, 15] * List.formPerm [16, 35] * List.formPerm [17, 31] * List.formPerm [20, 26] * List.formPerm [21, 46] * List.formPerm [23, 51] * List.formPerm [24, 53] * List.formPerm [25, 29] * List.formPerm [27, 50] * List.formPerm [28, 34] * List.formPerm [30, 39] * List.formPerm [32, 45] * List.formPerm [33, 61] * List.formPerm [36, 63] * List.formPerm [38, 48] * List.formPerm [43, 57] * List.formPerm [44, 52] * List.formPerm [49, 59] * List.formPerm [54, 58] * List.formPerm [60, 62]

@[expose] def xs : Fin 3 → Equiv.Perm (Fin 65) := ![tab xA, tab xB, tab xC]

@[expose] def ys : Fin 3 → Equiv.Perm (Fin 65) := ![tab yA, tab yB, tab yC]

@[expose] def cpt : Fin 65 := 37

@[expose] def allVec3 : List (Fin 3 → ZMod 2) :=
  [![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

@[expose] def allU : List (Fin 3 → Fin 3 → ZMod 2) :=
  allVec3.flatMap fun r0 => allVec3.flatMap fun r1 => allVec3.map fun r2 => ![r0, r1, r2]

end CFSG.GH74.KGroups.Sz8D
