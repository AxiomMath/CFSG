module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Quasithin.Recognition.CertF9
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.KGroups.A6

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix CFSG.Quasithin
@[expose] def pa : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 9] * List.formPerm [1, 2] * List.formPerm [4, 7] * List.formPerm [5, 8]

@[expose] def pb : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 7, 6, 1] * List.formPerm [3, 9, 4, 5]

@[expose] def sg0 : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 2, 4, 3, 5, 1] * List.formPerm [7, 8, 9]

@[expose] def sg1 : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 2] * List.formPerm [1, 5] * List.formPerm [3, 9] * List.formPerm [4, 8] * List.formPerm [6, 7]

@[expose] def QP : RawSchreierDatum 10 :=
  certificate (by decide) [pa, pb] [[-1, -2, 1, 2], [-3, -3, -1, -2, 3, 2]] #v[0, 1, 2] (by decide)

@[expose] def QA : RawSchreierDatum 10 :=
  certificate (by decide) [pa, pb, sg0, sg1] [[-3, 4], [-5, 2, -3], [6, 5, -6, -6, 5, 5]]
    #v[0, 1, 2, 3] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 5)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.A6
