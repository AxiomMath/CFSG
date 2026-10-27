module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Quasithin.Recognition.CertF8
import CFSG.Walter.PSL2Facts.Even
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
import CFSG.Walter.Defs

public section

namespace CFSG.GH74.KGroups.L28

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Quasithin CFSG.Blueprint Matrix
@[expose] def pa : Equiv.Perm (Fin 9) :=
  List.formPerm [0, 8] * List.formPerm [2, 5] * List.formPerm [3, 6] * List.formPerm [4, 7]

@[expose] def pb : Equiv.Perm (Fin 9) :=
  List.formPerm [0, 8, 5] * List.formPerm [1, 2, 3] * List.formPerm [4, 6, 7]

@[expose] def sg : Equiv.Perm (Fin 9) := List.formPerm [0, 4, 5, 2, 6, 3, 7, 1, 8]

@[expose] def QP : RawSchreierDatum 9 :=
  certificate (by decide) [pa, pb] [[-1, 2], [3, 3, 2, 3, 1, -3, -2]] #v[0, 1, 2] (by decide)

@[expose] def QA : RawSchreierDatum 9 :=
  certificate (by decide) [pa, pb, sg] [[-1, 2], [4, 4, -1, -3], [4, -5, 4], [6, 5, 6]]
    #v[0, 1, 2, 3] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 7)]

section Consequences

variable {K : Type} [Group K] (h : LieModel K .PSL 2 2 3)

include h

end Consequences

end CFSG.GH74.KGroups.L28
