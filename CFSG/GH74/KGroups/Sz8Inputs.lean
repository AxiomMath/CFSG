module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.NativeChecks
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.Blueprint.Catalog
public import CFSG.GH74.KGroups.PermAction
public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.LieType.Ree.SuzukiOvoidWeyl
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.LieType.Simplicity.Suzuki
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.NativeChecks
public meta import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public meta import Mathlib

public section

namespace CFSG.GH74.KGroups.Sz8

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Quasithin CFSG.LieType.Ree CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization
@[expose] def pa : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 55] * List.formPerm [1, 21] * List.formPerm [2, 15] * List.formPerm [3, 45] * List.formPerm [4, 50] * List.formPerm [5, 18] * List.formPerm [6, 46] * List.formPerm [7, 35] * List.formPerm [8, 11] * List.formPerm [9, 19] * List.formPerm [10, 60] * List.formPerm [12, 23] * List.formPerm [13, 34] * List.formPerm [14, 36] * List.formPerm [16, 56] * List.formPerm [17, 53] * List.formPerm [20, 44] * List.formPerm [22, 63] * List.formPerm [24, 58] * List.formPerm [26, 64] * List.formPerm [27, 48] * List.formPerm [28, 43] * List.formPerm [29, 51] * List.formPerm [30, 33] * List.formPerm [31, 61] * List.formPerm [32, 39] * List.formPerm [37, 40] * List.formPerm [38, 52] * List.formPerm [41, 47] * List.formPerm [42, 54] * List.formPerm [49, 59] * List.formPerm [57, 62]

@[expose] def pb : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 34, 63, 10] * List.formPerm [1, 39, 57, 31] * List.formPerm [2, 51, 28, 33] * List.formPerm [3, 59, 20, 14] * List.formPerm [4, 26, 21, 6] * List.formPerm [5, 30, 50, 25] * List.formPerm [8, 60, 53, 18] * List.formPerm [9, 54, 22, 11] * List.formPerm [12, 29, 43, 58] * List.formPerm [13, 23, 45, 47] * List.formPerm [15, 44, 55, 36] * List.formPerm [16, 64, 37, 35] * List.formPerm [17, 27, 19, 40] * List.formPerm [24, 42, 46, 38] * List.formPerm [32, 52, 41, 61] * List.formPerm [48, 49, 62, 56]

@[expose] def sg0 : Equiv.Perm (Fin 65) :=
  List.formPerm [3, 5, 7] * List.formPerm [4, 6, 8] * List.formPerm [11, 13, 15] * List.formPerm [12, 14, 16] * List.formPerm [17, 33, 49] * List.formPerm [18, 34, 50] * List.formPerm [19, 37, 55] * List.formPerm [20, 38, 56] * List.formPerm [21, 39, 51] * List.formPerm [22, 40, 52] * List.formPerm [23, 35, 53] * List.formPerm [24, 36, 54] * List.formPerm [25, 41, 57] * List.formPerm [26, 42, 58] * List.formPerm [27, 45, 63] * List.formPerm [28, 46, 64] * List.formPerm [29, 47, 59] * List.formPerm [30, 48, 60] * List.formPerm [31, 43, 61] * List.formPerm [32, 44, 62]

@[expose] def QP : RawSchreierDatum 65 :=
  certificate (by decide) [pa, pb] [[-1, 2, -1, -2, 1, 2, 1], [-1, -3, -2, -3, 2, 2], [3, 4, 4]] #v[0, 1, 2] (by decide)

@[expose] def QA : RawSchreierDatum 65 :=
  certificate (by decide) [pa, pb, sg0] [[2, 3, -2], [3, -4, -3, -4], [-5, 3, 5, 3]]
    #v[0, 3, 1, 2] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 13), ([false, true, false, true, true, false, true, true, true], 13)]

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

end Consequences

end CFSG.GH74.KGroups.Sz8
