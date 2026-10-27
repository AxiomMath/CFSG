module

public import Mathlib
public import CFSG.GH74.KGroups.Generic3
public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.KGroups.Generic7
public import CFSG.GH74.KGroups.M11Tables
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.M11Tables
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CFSG.GH74.KGroups.M11

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74 CFSG.GH74.Generic Subgroup
@[expose] def fw : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 9, 3] * List.formPerm [1, 4, 7] * List.formPerm [5, 10, 6]

@[expose] def fg1 : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 5, 6] * List.formPerm [1, 2, 9, 3, 4, 8] * List.formPerm [7, 10]

@[expose] def fg2 : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 9, 3, 4] * List.formPerm [1, 2, 7, 5]

end CFSG.GH74.KGroups.M11
