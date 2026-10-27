module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.KGroups.A5

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def pa : Equiv.Perm (Fin 5) :=
  List.formPerm [1, 2] * List.formPerm [3, 4]

@[expose] def pb : Equiv.Perm (Fin 5) :=
  List.formPerm [0, 1, 3]

@[expose] def sg0 : Equiv.Perm (Fin 5) :=
  List.formPerm [0, 3]

@[expose] def QP : RawSchreierDatum 5 :=
  certificate (by decide) [pa, pb] [[-1, 2, 1], [3, 2, -3, 1]] #v[1, 0, 2] (by decide)

@[expose] def QA : RawSchreierDatum 5 :=
  certificate (by decide) [pa, pb, sg0] [[-1, 2, 1], [-3, 4, 3], [-4, 5, 3]]
    #v[1, 0, 2, 3] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 5)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences
end CFSG.GH74.KGroups.A5
