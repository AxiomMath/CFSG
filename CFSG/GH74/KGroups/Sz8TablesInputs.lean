module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.NativeChecks
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.KGroups.Generic3
public import CFSG.GH74.KGroups.Sz8
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.NativeChecks
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.Sz8

public section

namespace CFSG.GH74.KGroups.Sz8

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def sy0 : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 47] * List.formPerm [1, 9] * List.formPerm [2, 55] * List.formPerm [3, 42] * List.formPerm [4, 56] * List.formPerm [5, 22] * List.formPerm [6, 18] * List.formPerm [7, 64] * List.formPerm [8, 14] * List.formPerm [10, 41] * List.formPerm [11, 19] * List.formPerm [12, 40] * List.formPerm [13, 15] * List.formPerm [16, 35] * List.formPerm [17, 31] * List.formPerm [20, 26] * List.formPerm [21, 46] * List.formPerm [23, 51] * List.formPerm [24, 53] * List.formPerm [25, 29] * List.formPerm [27, 50] * List.formPerm [28, 34] * List.formPerm [30, 39] * List.formPerm [32, 45] * List.formPerm [33, 61] * List.formPerm [36, 63] * List.formPerm [38, 48] * List.formPerm [43, 57] * List.formPerm [44, 52] * List.formPerm [49, 59] * List.formPerm [54, 58] * List.formPerm [60, 62]

@[expose] def sy1 : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 49] * List.formPerm [1, 16] * List.formPerm [2, 18] * List.formPerm [3, 32] * List.formPerm [4, 63] * List.formPerm [5, 60] * List.formPerm [6, 55] * List.formPerm [7, 25] * List.formPerm [8, 20] * List.formPerm [9, 35] * List.formPerm [10, 54] * List.formPerm [11, 12] * List.formPerm [13, 34] * List.formPerm [14, 26] * List.formPerm [15, 28] * List.formPerm [17, 21] * List.formPerm [19, 40] * List.formPerm [22, 62] * List.formPerm [23, 50] * List.formPerm [24, 38] * List.formPerm [27, 51] * List.formPerm [29, 64] * List.formPerm [30, 57] * List.formPerm [31, 46] * List.formPerm [33, 44] * List.formPerm [36, 56] * List.formPerm [39, 43] * List.formPerm [41, 58] * List.formPerm [42, 45] * List.formPerm [47, 59] * List.formPerm [48, 53] * List.formPerm [52, 61]

@[expose] def sy2 : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 21, 59, 31] * List.formPerm [1, 33, 35, 52] * List.formPerm [2, 40, 6, 11] * List.formPerm [3, 58, 45, 10] * List.formPerm [4, 13, 36, 28] * List.formPerm [5, 24, 62, 48] * List.formPerm [7, 51, 29, 50] * List.formPerm [8, 57, 26, 39] * List.formPerm [9, 61, 16, 44] * List.formPerm [12, 18, 19, 55] * List.formPerm [14, 43, 20, 30] * List.formPerm [15, 63, 34, 56] * List.formPerm [17, 47, 46, 49] * List.formPerm [22, 53, 60, 38] * List.formPerm [23, 25, 27, 64] * List.formPerm [32, 41, 42, 54]

@[expose] def sy3 : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 20] * List.formPerm [1, 3] * List.formPerm [2, 53] * List.formPerm [4, 29] * List.formPerm [5, 19] * List.formPerm [6, 38] * List.formPerm [7, 36] * List.formPerm [8, 49] * List.formPerm [9, 42] * List.formPerm [10, 52] * List.formPerm [11, 22] * List.formPerm [12, 62] * List.formPerm [13, 50] * List.formPerm [14, 59] * List.formPerm [15, 27] * List.formPerm [16, 32] * List.formPerm [17, 57] * List.formPerm [18, 48] * List.formPerm [21, 30] * List.formPerm [23, 34] * List.formPerm [24, 55] * List.formPerm [25, 56] * List.formPerm [26, 47] * List.formPerm [28, 51] * List.formPerm [31, 43] * List.formPerm [33, 58] * List.formPerm [35, 45] * List.formPerm [39, 46] * List.formPerm [40, 60] * List.formPerm [41, 44] * List.formPerm [54, 61] * List.formPerm [63, 64]

@[expose] def sy4 : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 45, 26, 16] * List.formPerm [1, 49, 42, 14] * List.formPerm [2, 29, 24, 56] * List.formPerm [3, 8, 9, 59] * List.formPerm [4, 55, 25, 53] * List.formPerm [5, 28, 11, 23] * List.formPerm [6, 7, 48, 63] * List.formPerm [10, 30, 44, 46] * List.formPerm [12, 50, 60, 15] * List.formPerm [13, 40, 27, 62] * List.formPerm [17, 58, 43, 61] * List.formPerm [18, 64, 38, 36] * List.formPerm [19, 51, 22, 34] * List.formPerm [20, 35, 47, 32] * List.formPerm [21, 41, 39, 52] * List.formPerm [31, 54, 57, 33]

@[expose] def sy5 : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 5, 8, 40] * List.formPerm [1, 28, 32, 27] * List.formPerm [2, 43, 48, 46] * List.formPerm [3, 51, 16, 15] * List.formPerm [4, 44, 64, 58] * List.formPerm [6, 30, 24, 17] * List.formPerm [7, 54, 56, 52] * List.formPerm [9, 34, 45, 50] * List.formPerm [10, 36, 61, 25] * List.formPerm [11, 59, 62, 26] * List.formPerm [12, 47, 22, 14] * List.formPerm [13, 42, 23, 35] * List.formPerm [18, 39, 53, 31] * List.formPerm [19, 49, 60, 20] * List.formPerm [21, 55, 57, 38] * List.formPerm [29, 41, 63, 33]

@[expose] def tt : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 27, 36, 33, 5, 57, 45] * List.formPerm [1, 26, 15, 4, 41, 60, 43] * List.formPerm [2, 48, 53, 24, 18, 38, 6] * List.formPerm [3, 8, 51, 63, 10, 11, 17] * List.formPerm [7, 52, 40, 30, 32, 14, 13] * List.formPerm [9, 49, 50, 29, 54, 19, 39] * List.formPerm [12, 31, 35, 59, 28, 56, 61] * List.formPerm [16, 20, 23, 25, 44, 22, 46] * List.formPerm [21, 42, 47, 34, 64, 58, 62]

@[expose] def QS : RawSchreierDatum 65 :=
  certificate (by decide) [sy0, sy1, sy2, sy3, sy4, sy5] []
    #v[0] (by decide)

section Tables

variable {K : Type} [Group K]

end Tables

end CFSG.GH74.KGroups.Sz8
