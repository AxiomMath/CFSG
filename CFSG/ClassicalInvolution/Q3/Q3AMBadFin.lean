module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.ClassicalInvolution.Uniform.UInduction
public import CFSG.ClassicalInvolution.Uniform.USat
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Statements

@[expose] def TwinBridge3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      A2Configuration z (satU (.sl2 3 1) K z) →
      ¬ CFSG.ClassicalInvolution.DeltaConnected (satU (.sl2 3 1) K z) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (satU (.sl2 3 1) K z),
        K' ≠ satU (.sl2 3 1) K z) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥

end Statements

end CFSG.ClassicalInvolution.Q3.Q3AM
