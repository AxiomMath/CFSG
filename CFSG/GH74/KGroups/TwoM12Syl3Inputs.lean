module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.TwoM12Aut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public meta import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.SectionalRank
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.GH74.KGroups.TwoM12

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint Subgroup
open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.GH74.E2 (Shape2M12)
set_option compiler.extract_closed false

@[expose] def x27 : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 4, 11] * List.formPerm [3, 7, 6] * List.formPerm [5, 8, 9]

@[expose] def y27 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 8, 6] * List.formPerm [2, 5, 3] * List.formPerm [7, 10, 9]

@[expose] def Q27 : RawSchreierDatum 12 :=
  certificate (by decide) [x27, y27] [[-1, 2, 1]] #v[1, 0] (by decide)

variable {K : Type} [Group K]

end CFSG.GH74.KGroups.TwoM12
