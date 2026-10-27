module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdONanB2
public import CFSG.LocalAnalysis.ComponentClassification.AS81Open
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Open
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuH1Final
public import CFSG.Sporadic.SuzRecog.MixedCell
public import CFSG.Sporadic.SuzRecog.SuzLeaf
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Size
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem rankTwoL3FourStandard_holds :
    RankTwoL3FourStandard :=
  rankTwoL3FourStandard_of_rankTwoL3EvenStandard
    (ComponentClassification.AS81.rankTwoL3EvenStandard_of_open
      (ComponentClassification.GMS78.rankTwoBenderStandard_of_open
        ComponentClassification.GMS78.ruH1Stmt)
      Sporadic.SuzRecog.MixedCell.mixedCellDichotomy)

section RankTwo


section Order

theorem ct_odd_standard_recognition_frontier_of_rankTwo
    (hB : AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hOddLie : OddLieThm187b)
    (hU : KProperSimpleUnbalancedUOutcome)
    (hBal : HeStandardBalanced)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Recognition.Exact.OddStandardType (L ⧸ center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card G ∈ lieOrdersChar p) ∨
      Nat.card G ∈ standardComponentOddSporadicOrders :=
  ct_odd_standard_recognition_frontier_of_onanProved hB hCIT hGH hOddLie
    rankTwoL3FourStandard_holds hU hBal G hnonab hK L hL htype

end Order

theorem ct_odd_standard_recognition_frontier_models_of_rankTwo
    (hB : AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hOddLie : OddLieThm187b)
    (hU : KProperSimpleUnbalancedUOutcome)
    (hBal : HeStandardBalanced)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Recognition.Exact.OddStandardType (L ⧸ center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨ Blueprint.OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS ∨
        IsSporadic G .McL ∨ IsSporadic G .Ly ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨
        IsSporadic G .ONan) :=
  ct_odd_standard_recognition_frontier_models_of_onanProved hB hCIT hGH hOddLie
    rankTwoL3FourStandard_holds hU hBal G hnonab hK L hL htype

end RankTwo

end CFSG.OddStandard
