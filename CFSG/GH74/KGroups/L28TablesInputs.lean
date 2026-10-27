module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.L28
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.L28

public section

namespace CFSG.GH74.KGroups.L28

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def sy0 : Equiv.Perm (Fin 9) :=
  List.formPerm [0, 6] * List.formPerm [1, 2] * List.formPerm [4, 8] * List.formPerm [5, 7]

@[expose] def sy1 : Equiv.Perm (Fin 9) :=
  List.formPerm [0, 1] * List.formPerm [2, 6] * List.formPerm [4, 7] * List.formPerm [5, 8]

@[expose] def sy2 : Equiv.Perm (Fin 9) :=
  List.formPerm [0, 4] * List.formPerm [1, 7] * List.formPerm [2, 5] * List.formPerm [6, 8]

@[expose] def QS : RawSchreierDatum 9 :=
  certificate (by decide) [sy0, sy1, sy2] []
    #v[0] (by decide)

section Tables

variable {K : Type} [Group K]

end Tables

end CFSG.GH74.KGroups.L28
