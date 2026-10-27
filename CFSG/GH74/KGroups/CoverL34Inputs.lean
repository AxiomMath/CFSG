
module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.Checks3
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.KGroups.L34Base
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.GH74.KGroups.L34Base
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def eg0 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 6] * List.formPerm [2, 10] * List.formPerm [3, 18] * List.formPerm [4, 14] * List.formPerm [7, 8] * List.formPerm [11, 16] * List.formPerm [12, 19] * List.formPerm [15, 20] * List.formPerm [26, 27] * List.formPerm [28, 29] * List.formPerm [30, 31] * List.formPerm [32, 33] * List.formPerm [34, 35] * List.formPerm [36, 37] * List.formPerm [38, 39] * List.formPerm [40, 41]

@[expose] def eg1 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 8] * List.formPerm [2, 20] * List.formPerm [3, 16] * List.formPerm [4, 12] * List.formPerm [6, 7] * List.formPerm [10, 15] * List.formPerm [11, 18] * List.formPerm [14, 19] * List.formPerm [26, 28] * List.formPerm [27, 29] * List.formPerm [30, 32] * List.formPerm [31, 33] * List.formPerm [34, 36] * List.formPerm [35, 37] * List.formPerm [38, 40] * List.formPerm [39, 41]

@[expose] def eg2 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 2] * List.formPerm [3, 4] * List.formPerm [6, 10] * List.formPerm [7, 15] * List.formPerm [8, 20] * List.formPerm [11, 19] * List.formPerm [12, 16] * List.formPerm [14, 18] * List.formPerm [22, 23] * List.formPerm [24, 25] * List.formPerm [30, 31] * List.formPerm [32, 33] * List.formPerm [34, 36] * List.formPerm [35, 37] * List.formPerm [38, 41] * List.formPerm [39, 40]

@[expose] def eg3 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 4] * List.formPerm [2, 3] * List.formPerm [6, 14] * List.formPerm [7, 19] * List.formPerm [8, 12] * List.formPerm [10, 18] * List.formPerm [11, 15] * List.formPerm [16, 20] * List.formPerm [22, 24] * List.formPerm [23, 25] * List.formPerm [30, 32] * List.formPerm [31, 33] * List.formPerm [34, 37] * List.formPerm [35, 36] * List.formPerm [38, 39] * List.formPerm [40, 41]

@[expose] def QE : RawSchreierDatum 42 :=
  certificate (by decide) [eg0, eg1, eg2, eg3] [] #v[0] (by decide)

@[expose] def cws : List (List ℤ) :=
  [[2, 1, 2, 1, 2, 1, -2], [-2, 1, 2, 1, -2, 1, 2], [2, 2, 1, -2, 1, 2, 1, 2, 1], [], [-2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1], [1, -2, 1, 2, 1, -2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1], [1, 2, 2, 1, 2, 2, 1], [2, 1, 2, 1, -2, 1, -2], [2, 1, 2, 2, 1, -2], [-2, 1, -2, 1, -2, 1, 2, 1], [1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1], [1, 2, 1, 2, 1, -2, 1], [1, -2, 1, -2, 1, 2, 1, 2, 2], [2, 1, -2, 1, -2, 1, -2]]

end CFSG.GH74.KGroups.L34
