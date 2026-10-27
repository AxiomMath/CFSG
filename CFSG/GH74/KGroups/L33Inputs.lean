module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib

public section

namespace CFSG.GH74.KGroups.L33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix
@[expose] def pa : Equiv.Perm (Fin 13) :=
  List.formPerm [0, 12] * List.formPerm [3, 11] * List.formPerm [4, 7] * List.formPerm [6, 10]

@[expose] def pb : Equiv.Perm (Fin 13) :=
  List.formPerm [0, 11, 4] * List.formPerm [1, 12, 9] * List.formPerm [2, 10, 7] * List.formPerm [5, 6, 8]

@[expose] def pa' : Equiv.Perm (Fin 13) :=
  List.formPerm [0, 12] * List.formPerm [3, 11] * List.formPerm [4, 7] * List.formPerm [6, 10]

@[expose] def pb' : Equiv.Perm (Fin 13) :=
  List.formPerm [0, 2, 9] * List.formPerm [1, 5, 3] * List.formPerm [4, 11, 10] * List.formPerm [6, 12, 8]

@[expose] def PA : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 12] * List.formPerm [3, 11] * List.formPerm [4, 7] * List.formPerm [6, 10] * List.formPerm [13, 25] * List.formPerm [16, 24] * List.formPerm [17, 20] * List.formPerm [19, 23]

@[expose] def PB : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 11, 4] * List.formPerm [1, 12, 9] * List.formPerm [2, 10, 7] * List.formPerm [5, 6, 8] * List.formPerm [13, 15, 22] * List.formPerm [14, 18, 16] * List.formPerm [17, 24, 23] * List.formPerm [19, 25, 21]

@[expose] def sg0 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 18, 3, 16, 9, 17] * List.formPerm [1, 20, 8, 15, 2, 24] * List.formPerm [4, 22, 10, 21, 7, 14] * List.formPerm [5, 19, 12, 13, 11, 23] * List.formPerm [6, 25]

@[expose] def QP13 : RawSchreierDatum 13 :=
  certificate (by decide) [pa, pb] [[-1, -2, 1, 2, 1], [-2, 3, 1], [-4, 3, 4], [4, -3, 5, 4, 3], [-5, -6], [-3, -7, -4, 3], [-5, -8, -6, 5]] #v[0, 1, 3, 2, 4] (by decide)

@[expose] def QP : RawSchreierDatum 26 :=
  certificate (by decide) [PA, PB] [[-1, -2, 1, 2, 1], [-2, 3, 1], [-4, 3, 4], [4, -3, 5, 4, 3], [-5, -6], [-3, -7, -4, 3], [-5, -8, -6, 5]] #v[0, 1, 3, 2, 4] (by decide)

@[expose] def QA : RawSchreierDatum 26 :=
  certificate (by decide) [PA, PB, sg0] [[-1, -3, -3, 2], [-4, -4, -4, -4], [-2, 4, 1], [4, -6, 4], [-5, 7, 5], [-7, -5, -6, -4, 6, 6]]
    #v[0, 1, 2, 3, 4] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 13), ([false, true, false, true, true], 6)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.L33
