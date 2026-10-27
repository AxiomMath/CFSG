module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedCentral
public import CFSG.ClassicalInvolution.Q3.Q3WLift
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSwap
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W

section Statements

@[expose] def IsProductElt3 {G : Type} [Group G] (K M : Subgroup G) (x : G) : Prop :=
  Commutes K M ∧ x ∈ K ⊔ M ∧ orderOf x = 2 ∧ x ∉ K ∧ x ∉ M

end Statements

end CFSG.ClassicalInvolution.Q3.Q3OF
