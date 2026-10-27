module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.Checks3
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.Generic.Shapes
public import CFSG.Sporadic.Schreier.M23Gens
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.Sporadic.Schreier.M23Gens
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

namespace CFSG.GH74.KGroups.M23

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def QP : RawSchreierDatum 23 :=
  certificate (by decide) [m23PermA, m23PermB] [[-1, 2, 1, -2, 1], [-2, 3, 2], [-2, -1, 4, 2], [5, -4, -1, 5, 1, 2], [-1, 6, 1], [-6, 7, -3, -5, -7, -1, 5, 4, 2], [8, -6, -7, -6, -8, -1, 8, 1], [-1, 9, 1], [-7, -10, -1, 8, 1], [8, -11, -6, -9, -1, -11, 1], [-12, -1, 12, 1], [-12, -11, -6, 7, 5, -10, -1, 5, 4, 2]] #v[0, 1, 2, 3, 4, 5] (by decide)

@[expose] def eg0 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]

@[expose] def eg1 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 18] * List.formPerm [3, 19] * List.formPerm [4, 17] * List.formPerm [6, 15] * List.formPerm [7, 14] * List.formPerm [10, 22] * List.formPerm [20, 21]

@[expose] def eg2 : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 20] * List.formPerm [1, 21] * List.formPerm [2, 18] * List.formPerm [3, 19] * List.formPerm [6, 14] * List.formPerm [7, 15] * List.formPerm [8, 12] * List.formPerm [9, 13]

@[expose] def eg3 : Equiv.Perm (Fin 23) :=
  List.formPerm [2, 3] * List.formPerm [4, 10] * List.formPerm [6, 15] * List.formPerm [7, 14] * List.formPerm [8, 12] * List.formPerm [9, 13] * List.formPerm [17, 22] * List.formPerm [18, 19]

@[expose] def QE : RawSchreierDatum 23 :=
  certificate (by decide) [eg0, eg1, eg2, eg3] [[-1, 2]] #v[0, 2] (by decide)

@[expose] def cws : List (List ℤ) :=
  [[2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2], [-2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2], [-2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2], [-2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2], [], [2, 1, -2, 1, -2, 1, 2, 2, 1, -2, 1, -2], [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2], [2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2], [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2], [-2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2], [-2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2], [-2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2], [2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2], [2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2], [-2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2]]

end CFSG.GH74.KGroups.M23
