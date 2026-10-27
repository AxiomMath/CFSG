module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.M11
public import CFSG.RankThree.Asc83Table.GL23
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.M11

public section

namespace CFSG.GH74.KGroups.M11

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def sR : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 1, 8, 4, 7, 9, 2, 3] * List.formPerm [6, 10]

@[expose] def sT : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 4] * List.formPerm [2, 8] * List.formPerm [3, 9] * List.formPerm [6, 10]

@[expose] def s0 : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 7] * List.formPerm [1, 9] * List.formPerm [2, 8] * List.formPerm [3, 4]

@[expose] def t0 : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 9] * List.formPerm [1, 5] * List.formPerm [4, 6] * List.formPerm [7, 10]

@[expose] def QS : RawSchreierDatum 11 :=
  certificate (by decide) [sR, sT] []
    #v[0, 1] (by decide)

section Tables

variable {K : Type} [Group K] (e : K ≃* Q.originalSubgroup)

include e

end Tables

end CFSG.GH74.KGroups.M11
