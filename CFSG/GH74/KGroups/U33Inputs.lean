module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Perm
import CFSG.Timmesfeld.Final.PSU33
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.GH74.KGroups.U33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def pa : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 1, 10] * List.formPerm [2, 26, 12] * List.formPerm [3, 24, 11] * List.formPerm [4, 21, 18] * List.formPerm [5, 22, 6] * List.formPerm [7, 20, 14] * List.formPerm [8, 9, 25] * List.formPerm [13, 15, 23] * List.formPerm [16, 17, 27]

@[expose] def pb : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 12, 10] * List.formPerm [1, 13, 6] * List.formPerm [2, 27, 22] * List.formPerm [3, 7, 18] * List.formPerm [4, 16, 23] * List.formPerm [5, 8, 20] * List.formPerm [9, 26, 15] * List.formPerm [14, 21, 24] * List.formPerm [17, 25, 19]

@[expose] def sg0 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 14, 7, 25, 4, 11, 1, 22] * List.formPerm [2, 3, 9, 8, 10, 19, 17, 27] * List.formPerm [5, 24, 15, 16, 6, 21, 23, 13] * List.formPerm [12, 18, 20, 26]

@[expose] def QP : RawSchreierDatum 28 :=
  certificate (by decide) [pa, pb] [[1, -2], [-2, 3, 1, 2, 1], [4, 3, 3], [-5, -5]] #v[0, 1, 2, 4] (by decide)

@[expose] def QA : RawSchreierDatum 28 :=
  certificate (by decide) [pa, pb, sg0] [[1, -2], [3, 3, 1], [-4, -4, 5, 4], [-4, 6, -1, 5, 3, 2], [7, 4, -1, 2, -6, 2]]
    #v[0, 1, 4, 2] (by decide)

@[expose] def pu : Equiv.Perm (Fin 28) :=
  List.formPerm [4, 7] * List.formPerm [5, 8] * List.formPerm [6, 9] * List.formPerm [10, 19] * List.formPerm [11, 20] * List.formPerm [12, 21] * List.formPerm [13, 25] * List.formPerm [14, 26] * List.formPerm [15, 27] * List.formPerm [16, 22] * List.formPerm [17, 23] * List.formPerm [18, 24]

@[expose] def pv : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 16, 3, 8, 23, 14, 20] * List.formPerm [1, 12, 25, 10, 13, 15, 2] * List.formPerm [4, 9, 11, 22, 5, 24, 7] * List.formPerm [6, 19, 18, 26, 27, 21, 17]

@[expose] def pt2 : Equiv.Perm (Fin 28) :=
  List.formPerm [2, 3] * List.formPerm [5, 6] * List.formPerm [8, 9] * List.formPerm [10, 19] * List.formPerm [11, 21] * List.formPerm [12, 20] * List.formPerm [13, 22] * List.formPerm [14, 24] * List.formPerm [15, 23] * List.formPerm [16, 25] * List.formPerm [17, 27] * List.formPerm [18, 26]

@[expose] def px1 : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 2, 3] * List.formPerm [4, 5, 6] * List.formPerm [7, 8, 9] * List.formPerm [10, 11, 12] * List.formPerm [13, 14, 15] * List.formPerm [16, 17, 18] * List.formPerm [19, 20, 21] * List.formPerm [22, 23, 24] * List.formPerm [25, 26, 27]

@[expose] def px2 : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 4, 7] * List.formPerm [2, 5, 8] * List.formPerm [3, 6, 9] * List.formPerm [10, 15, 17] * List.formPerm [11, 13, 18] * List.formPerm [12, 14, 16] * List.formPerm [19, 23, 27] * List.formPerm [20, 24, 25] * List.formPerm [21, 22, 26]

@[expose] def wsU : List (List Bool × ℕ) := [([false, true], 6)]

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 7), ([false, false, true, false, true], 4)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.U33
