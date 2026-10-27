module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizerBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.SeitzReduction.RankOne
