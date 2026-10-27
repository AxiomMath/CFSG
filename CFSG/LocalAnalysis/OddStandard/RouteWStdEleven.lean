module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdTwelve
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoEleven

public section

namespace CFSG.OddStandard

namespace AltStdSec

open CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd.Spor

section Tri


theorem exactShapeTrichotomy_holds : ExactShapeTrichotomy :=
  exactShapeTrichotomy_of_lookup
    (altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
      CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
      co1LocalComponentsInput_holds hnLocalComponentsInput_holds
      (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)
      lyOuterTrivialInput Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
      CatLeafProof.monsterInnerInput CatLeafProof.monsterLocalComponentsInput)
    hnLocalComponentsInput_holds RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds

end Tri

section Holds


theorem shapeTwoSmallEleven_of_ten_holds (h10 : ShapeTwoSmallTen) : ShapeTwoSmallEleven :=
  shapeTwoSmallEleven_of_ten exactShapeTrichotomy_holds SeitzReduction.gls3OddLieAutComponentsInput
    CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
    (RankTwoAlt.rankTwoAlternatingStandard_of_open
        (RankTwoAltFive.altFiveCaseI_of
            (RankTwoAlt.altGenerationFive_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA))
        (RankTwoAltFive.asc310EpsOne_of Asc76X.goldschmidtTheoremA) RankTwoAltFive.asc310IIb
        RankTwoAlt.altFiveM12NotTop_of RankTwoAlt.altEvenCenterSmall RankTwoAlt.altThreeCover
        (RankTwoAlt.altGenerationSmall_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA)
        RankTwoAlt.altRootFusion
        (RankTwoAlt.altTypeTwoFusion_of_rootFusion RankTwoAlt.altRootFusion)
        (RankTwoAlt.altTypeTwoCentralizer Asc76X.goldschmidtTheoremA)) h10

end Holds

end AltStdSec

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem ct_odd_standard_recognition_frontier_of_shapeTwoTen
    (hIS : AltStdSec.AltStdBalancedOrder2InnerSmall) (hS10 : AltStdSec.ShapeTwoSmallTen)
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
  ct_odd_standard_recognition_frontier_of_twelve hIS
    (AltStdSec.shapeTwoSmallEleven_of_ten_holds hS10) hCIT hGH hOddLie hU hP2 G hnonab hK L hL
    htype

theorem ct_odd_standard_recognition_frontier_models_of_shapeTwoTen
    (hIS : AltStdSec.AltStdBalancedOrder2InnerSmall) (hS10 : AltStdSec.ShapeTwoSmallTen)
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
  ct_odd_standard_recognition_frontier_models_of_twelve hIS
    (AltStdSec.shapeTwoSmallEleven_of_ten_holds hS10) hCIT hGH hOddLie hU hP2 G hnonab hK L hL
    htype

end CFSG.OddStandard
