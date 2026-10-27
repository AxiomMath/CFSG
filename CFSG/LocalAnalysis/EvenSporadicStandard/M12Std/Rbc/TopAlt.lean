module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdEleven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenNoPartner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenL44
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4CTOdd
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UMain
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwFinal
import CFSG.LocalAnalysis.OddStandard.ChildLargeAltAt
import CFSG.LocalAnalysis.OddStandard.ChildSmallAltOddAt

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.OddStandard CFSG.OddStandard.AltStdSec

variable {G : Type} [Group G] [Finite G]

private theorem oddOutcome_of_childLargeAltW
    (h : AltOutcome G ∨ OddLieType G ∨ IsSporadic G .McL ∨ IsSporadic G .Ly) : OddOutcome G := by
  unfold OddOutcome
  tauto

private theorem oddOutcome_of_childSmallAltOdd
    (h : AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)) :
    OddOutcome G := by
  unfold OddOutcome
  tauto

section Certified


theorem alt_top_outcome
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput)
    (h6 : HSMcLLyExclusion) (h7 : TwoHSGivesHN) {X : Subgroup G} (hX : StdHyp G X)
    {m : ℕ} (hm : 5 ≤ m)
    (hA : Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin m))) :
    OddOutcome G := by
  have hU : SmallF3Interfaces.UImplication G := by
    rintro ⟨z, hz2, hne⟩
    exact absurd (hX.oddCore z hz2) hne
  have hS : StandardSetting G X := ⟨hX.simple, hX.nonabelian, hX.kProper, hX.standard⟩
  have hRank2 : CFSG.ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard :=
    ComponentClassification.RankTwoAlt.rankTwoAlternatingStandard_of_open
        (ComponentClassification.RankTwoAltFive.altFiveCaseI_of
            (ComponentClassification.RankTwoAlt.altGenerationFive_of
                ComponentClassification.AS76b.asc08Lemma34
                ComponentClassification.Asc76X.goldschmidtTheoremA))
        (ComponentClassification.RankTwoAltFive.asc310EpsOne_of
            ComponentClassification.Asc76X.goldschmidtTheoremA)
        ComponentClassification.RankTwoAltFive.asc310IIb
        ComponentClassification.RankTwoAlt.altFiveM12NotTop_of
        ComponentClassification.RankTwoAlt.altEvenCenterSmall
        ComponentClassification.RankTwoAlt.altThreeCover
        (ComponentClassification.RankTwoAlt.altGenerationSmall_of
            ComponentClassification.AS76b.asc08Lemma34
            ComponentClassification.Asc76X.goldschmidtTheoremA)
        ComponentClassification.RankTwoAlt.altRootFusion
        (ComponentClassification.RankTwoAlt.altTypeTwoFusion_of_rootFusion
            ComponentClassification.RankTwoAlt.altRootFusion)
        (ComponentClassification.RankTwoAlt.altTypeTwoCentralizer
            ComponentClassification.Asc76X.goldschmidtTheoremA)
  have hHSF : CFSG.ComponentClassification.GSLit.HarrisSolomonFritzInput :=
    ComponentClassification.HSFLit.hsflit_of_steps hGH OddStandard.Harada75.haradaInput_holds
        (CFSG.ComponentClassification.GHarris.gorensteinHarrisInput_of
            (ThmC.leaf_of_full
                (ThmC.thmCFull_of_route ThmC.O2.o2Structure
                    (ThmC.Core.normalSimpleCore_of_hyps
                        (ThmC.O2.o2Structure_of_gor42 ThmC.O2.Gor.gor42) ThmC.O2.Gor.gor42)
                    (ThmC.simpleCase_of_gh74 hGH ThmC.sylowComparison) ThmC.l34IndexThree)
                ThmC.l34OneClass) CFSG.Quasithin.HSType.statementI48_holds)
        ComponentClassification.HSFLit.ghPresentationBound ComponentClassification.HSFLit.ghRelInHS
        ComponentClassification.HSFLit.Sec8.fritz812dNotSylow
        ComponentClassification.HSDihedral.FritzL2.fritzL2Lemma36Final
        ComponentClassification.HSDihedral.FritzL2.fritzL2Lemma378
        ComponentClassification.HSFLit.fritzL2KDFacts ComponentClassification.HSFLit.fritzKDSection4
        ComponentClassification.HSFLit.fritzKDSection6
        ComponentClassification.HSFLit.fritzKDSection7
        (ComponentClassification.HSFLit.KD8ab.fritzKDSection8ab_of_cases
            CFSG.ComponentClassification.HSFLit.KD8ab.caseA
            CFSG.ComponentClassification.HSFLit.KD8abB.caseB)
        CFSG.ComponentClassification.HSFLit.KD8c.fritzKDSection8c
  have hHS : ShapeTwoTenStdHS :=
    shapeTwoTenStdHS_of_parts' CFSG.SeitzReduction.gls3OddLieAutComponentsInput
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput shapeTwoTenL44Excl_holds
      (shapeTwoTenNoSwapPartnerNoCentralStdHS_of_inputs
        CFSG.SeitzReduction.gls3OddLieAutComponentsInput
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput shapeTwoTenL44Excl_holds)
      (SwapPartner.shapeTwoTenSwapPartnerStdHS_of_frames SwapPartner.ys04a_holds
        SwapPartner.ys04b_holds)
  have hB : AltStdCyclicBalancedFalse :=
    altStdCyclicBalancedFalse_of_small_eleven
      AltStdSmall4.CTOdd.altStdBalancedOrder2InnerSmall_holds
      (shapeTwoSmallEleven_of_ten_holds
        (shapeTwoSmallTen_of_nine AltStdSmall4.CTOdd.shapeTwoSmallNine_holds hHS h6 h7))
      shapeTwoCentDoubleAt_twelve_holds
  rcases le_or_gt 8 m with h8 | h8
  · exact oddOutcome_of_childLargeAltW (childLargeAltWAt_of_inputsStd
      (alternatingStandardFormInputWAt_of_rankOneAt hRank2
        (altStdRankOneWAt_of_cyclicWAt hCIT (altStdCyclicWAt_of_balancedFalse hU hB)))
      (Solomon75.solomon2AnStdW_of_cyclic hRank2 hCIT (solomon2AnStdCyclic_holds hGH))
      X hS ⟨m, h8, hA⟩)
  · rcases Nat.even_or_odd (Nat.card (center X)) with hev | hodd
    · exact Or.inr (Or.inl (childSmallAltEven_of_classicalInvolution hCIT G X hS
        ⟨m, hm, by omega, hA⟩ hev))
    · exact oddOutcome_of_childSmallAltOdd (childSmallAltOddAt_of_inputs hRank2 hCIT hHSF
        (smallAltFiveCyclicAt_of_inputs hU Harada75.haradaInput_holds hGH) X hS
        ⟨m, hm, by omega, hA⟩ hodd)

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
