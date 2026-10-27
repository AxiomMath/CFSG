module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.Checks3
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.Generic.Shapes
public import CFSG.Sporadic.Mathieu.M22
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.Sporadic.Mathieu.M22
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

namespace CFSG.GH74.KGroups.M22

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
@[expose] def QP : RawSchreierDatum 22 :=
  certificate (by decide) [m22gA, m22gB] [[2, 1, -2], [-1, -3, 1, 3, 1], [-2, -4, 1, 2, 1], [-4, 5, 4], [-5, 3, 5], [-6, -7, 6, 7, 6], [-4, -7, -1, 6, 1], [-6, -7, -9, 6], [-2, -2, 5, 2], [11, 6, 3], [9, -12, 6], [-8, -13]] #v[0, 1, 2, 3, 4] (by decide)

@[expose] def eg0 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 3] * List.formPerm [1, 7] * List.formPerm [2, 20] * List.formPerm [4, 8] * List.formPerm [6, 12] * List.formPerm [11, 16] * List.formPerm [13, 14] * List.formPerm [19, 21]

@[expose] def eg1 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 4] * List.formPerm [1, 14] * List.formPerm [2, 20] * List.formPerm [3, 8] * List.formPerm [5, 15] * List.formPerm [6, 12] * List.formPerm [7, 13] * List.formPerm [9, 18]

@[expose] def eg2 : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 13] * List.formPerm [2, 20] * List.formPerm [5, 18] * List.formPerm [6, 12] * List.formPerm [7, 14] * List.formPerm [9, 15] * List.formPerm [11, 21] * List.formPerm [16, 19]

@[expose] def eg3 : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 8] * List.formPerm [1, 14] * List.formPerm [2, 6] * List.formPerm [3, 4] * List.formPerm [7, 13] * List.formPerm [11, 21] * List.formPerm [12, 20] * List.formPerm [16, 19]

@[expose] def QE : RawSchreierDatum 22 :=
  certificate (by decide) [eg0, eg1, eg2, eg3] [[-4, 2, 1]] #v[0, 1] (by decide)

@[expose] def cws : List (List ℤ) :=
  [[1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2], [-2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1], [-2, 1, 2, 2, 1, 2], [-2, 1, 2, 1, -2, 1, 2], [], [1, 2, 1, 2, 1, -2, 1], [2, 2, 1, -2, 1, 2, 2, 1, 2, 1], [-2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1], [-2, 1, -2, 1, -2, 1, 2], [2, 2, 1, 2, 1, 2, 1, 2, 2], [-2, 1, 2, 1, 2, 2, 1, -2, 1, 2], [1, 2, 1, -2, 1], [1, 2, 2, 1, -2, 1], [1, 2, 2, 1, -2, 1, 2, 1, -2], [-2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1]]

end CFSG.GH74.KGroups.M22
