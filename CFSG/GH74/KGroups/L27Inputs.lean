module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.GH74.KGroups.PrimeField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib

public section

namespace CFSG.GH74.KGroups.L27

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix
@[expose] def pa : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 7] * List.formPerm [1, 6] * List.formPerm [2, 3] * List.formPerm [4, 5]

@[expose] def pb : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 7, 1] * List.formPerm [2, 4, 6]

@[expose] def sg0 : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 2, 1, 4, 7, 3, 6, 5]

@[expose] def QP : RawSchreierDatum 8 :=
  certificate (by decide) [pa, pb] [[-1, 2], [-3, -3, 2, 3, -1, -3, -3, -2]] #v[0, 1, 2] (by decide)

@[expose] def QA : RawSchreierDatum 8 :=
  certificate (by decide) [pa, pb, sg0] [[-1, 2], [2, 3, 3], [4, -3, 5, 1]]
    #v[0, 1, 2] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 7)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.L27
