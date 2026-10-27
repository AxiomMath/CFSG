module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.GH74.KGroups.PrimeField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GH74.KGroups.L217

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix
@[expose] def pa : Equiv.Perm (Fin 18) :=
  List.formPerm [0, 17] * List.formPerm [1, 16] * List.formPerm [2, 8] * List.formPerm [3, 11] * List.formPerm [5, 10] * List.formPerm [6, 14] * List.formPerm [7, 12] * List.formPerm [9, 15]

@[expose] def pb : Equiv.Perm (Fin 18) :=
  List.formPerm [0, 17, 1] * List.formPerm [2, 9, 16] * List.formPerm [3, 12, 8] * List.formPerm [4, 5, 11] * List.formPerm [6, 15, 10] * List.formPerm [7, 13, 14]

@[expose] def sg0 : Equiv.Perm (Fin 18) :=
  List.formPerm [0, 16, 14, 1, 13, 4, 9, 12, 15, 3, 11, 6, 10, 8, 7, 17]

@[expose] def QP : RawSchreierDatum 18 :=
  certificate (by decide) [pa, pb] [[-1, 2], [2, 3, 3, -1, -3, -3, 2, 3, 1]] #v[0, 1, 2] (by decide)

@[expose] def QA : RawSchreierDatum 18 :=
  certificate (by decide) [pa, pb, sg0] [[-1, 2], [4, 4, -1, -3]]
    #v[0, 1, 2] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 17)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.L217
