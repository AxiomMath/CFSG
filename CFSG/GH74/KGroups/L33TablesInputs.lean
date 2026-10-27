module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.L33
public import CFSG.RankThree.Asc83Table.GL23
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.L33

public section

namespace CFSG.GH74.KGroups.L33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def sR : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 2, 6, 1, 4, 5, 7, 3] * List.formPerm [9, 12, 11, 10] * List.formPerm [14, 16, 21, 24] * List.formPerm [15, 19, 23, 20, 25, 22, 17, 18]

@[expose] def sT : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 6] * List.formPerm [2, 5] * List.formPerm [4, 7] * List.formPerm [10, 12] * List.formPerm [16, 24] * List.formPerm [17, 23] * List.formPerm [18, 22] * List.formPerm [19, 20]

@[expose] def s0 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 4] * List.formPerm [1, 3] * List.formPerm [2, 5] * List.formPerm [6, 7] * List.formPerm [15, 25] * List.formPerm [17, 23] * List.formPerm [18, 20] * List.formPerm [19, 22]

@[expose] def t0 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 1] * List.formPerm [6, 11] * List.formPerm [7, 10] * List.formPerm [8, 9] * List.formPerm [13, 16] * List.formPerm [15, 24] * List.formPerm [18, 23] * List.formPerm [21, 25]

@[expose] def QS : RawSchreierDatum 26 :=
  certificate (by decide) [sR, sT] [[-2, 1, 1]]
    #v[0, 1] (by decide)

section Tables

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Tables

end CFSG.GH74.KGroups.L33
