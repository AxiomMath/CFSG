module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdRankTwo
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHBSmall
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStableCentre

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem ct_odd_standard_recognition_frontier_of_heldKSwapped
    (hIS : AltStdSec.AltStdBalancedOrder2InnerSmall) (hS11 : AltStdSec.ShapeTwoSmallEleven)
    (h47 : AltStdSec.ShapeTwoCentDoubleAt 12)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hOddLie : OddLieThm187b)
    (hU : KProperSimpleUnbalancedUOutcome)
    (hP2 : ComponentClassification.GrSLit.HeldKSwapped)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Recognition.Exact.OddStandardType (L ⧸ center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card G ∈ lieOrdersChar p) ∨
      Nat.card G ∈ standardComponentOddSporadicOrders :=
  ct_odd_standard_recognition_frontier_of_rankTwo
    (AltStdSec.altStdCyclicBalancedFalse_of_small_eleven hIS hS11 h47) hCIT hGH hOddLie hU
    (ComponentClassification.GrSLit.heStandardBalanced_of_heldKSwapped hP2) G hnonab hK L hL htype

theorem ct_odd_standard_recognition_frontier_models_of_heldKSwapped
    (hIS : AltStdSec.AltStdBalancedOrder2InnerSmall) (hS11 : AltStdSec.ShapeTwoSmallEleven)
    (h47 : AltStdSec.ShapeTwoCentDoubleAt 12)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hOddLie : OddLieThm187b)
    (hU : KProperSimpleUnbalancedUOutcome)
    (hP2 : ComponentClassification.GrSLit.HeldKSwapped)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Recognition.Exact.OddStandardType (L ⧸ center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨ Blueprint.OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS ∨
        IsSporadic G .McL ∨ IsSporadic G .Ly ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨
        IsSporadic G .ONan) :=
  ct_odd_standard_recognition_frontier_models_of_rankTwo
    (AltStdSec.altStdCyclicBalancedFalse_of_small_eleven hIS hS11 h47) hCIT hGH hOddLie hU
    (ComponentClassification.GrSLit.heStandardBalanced_of_heldKSwapped hP2) G hnonab hK L hL htype

end CFSG.OddStandard
