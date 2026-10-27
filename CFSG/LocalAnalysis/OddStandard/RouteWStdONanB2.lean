module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdONan
public import CFSG.LocalAnalysis.OddStandard.ONanB2Mirror

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem ONanRec.sylowBal_ON_of_gh74
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput) :
    ONanRec.SylowBal NativeSporadic.ON :=
  ONanRec.sylowBal_ON_of_loc hGH ONanRec.B2.stageB2Loc_holds

section ONanProved


section Order


theorem ct_odd_standard_recognition_frontier_of_onanProved
    (hB : AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hOddLie : OddLieThm187b)
    (hRankL34 : RankTwoL3FourStandard)
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
  ct_odd_standard_recognition_frontier_of_onanLoc hB hCIT hGH hOddLie hRankL34
    ONanRec.B2.stageB2Loc_holds hU hBal G hnonab hK L hL htype

end Order

theorem ct_odd_standard_recognition_frontier_models_of_onanProved
    (hB : AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hOddLie : OddLieThm187b)
    (hRankL34 : RankTwoL3FourStandard)
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
  ct_odd_standard_recognition_frontier_models_of_onanLoc hB hCIT hGH hOddLie hRankL34
    ONanRec.B2.stageB2Loc_holds hU hBal G hnonab hK L hL htype

end ONanProved

end CFSG.OddStandard
