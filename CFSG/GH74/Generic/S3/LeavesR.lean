module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S45.GL42
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

@[expose] def OnlyInvX {G : Type} [Group G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ u ∈ centralizer (K : Set (CentralizerBar x)), orderOf u = 2 → u = xbar x

end CFSG.GH74.Generic.S3
