
module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L34Base
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.L34Base

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix
@[expose] def sg0 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 30] * List.formPerm [1, 32, 2, 21, 4, 31] * List.formPerm [3, 33] * List.formPerm [5, 39, 19, 27, 15, 41] * List.formPerm [6, 29, 18, 23, 13, 24] * List.formPerm [7, 25, 20, 40, 14, 35] * List.formPerm [8, 36, 17, 37, 16, 28] * List.formPerm [9, 26] * List.formPerm [10, 38, 12, 22, 11, 34]

@[expose] def sg1 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 16, 1, 4, 7, 19, 14, 20] * List.formPerm [2, 10, 11, 5, 9, 18, 13, 8] * List.formPerm [3, 17, 15, 12] * List.formPerm [21, 32, 41, 40, 36, 23, 30, 25] * List.formPerm [22, 31, 27, 39] * List.formPerm [24, 33, 34, 38, 28, 26, 37, 29]

@[expose] def sg2 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 40, 1, 22, 10, 29] * List.formPerm [2, 32, 14, 41, 9, 24] * List.formPerm [3, 28, 6, 37, 11, 34] * List.formPerm [4, 36, 18, 33, 12, 31] * List.formPerm [5, 23, 15, 38, 13, 21] * List.formPerm [7, 30, 19, 26, 8, 27] * List.formPerm [16, 39, 17, 25, 20, 35]

@[expose] def QA : RawSchreierDatum 42 :=
  certificate (by decide) [PA, PB, sg0, sg1, sg2] [[-4, -2], [-6, -6], [-3, -3], [-6, 8, 6], [-8, 9, 6], [-3, 5, 1], [-8, -11, 6, 11], [9, -12, 7], [-10, -13, -9, 12, 9, 12]]
    #v[0, 2, 5, 3, 1, 6] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 7), ([false, true, true], 5)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.L34
