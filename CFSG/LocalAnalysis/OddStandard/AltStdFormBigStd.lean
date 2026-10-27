module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdEleven
public import CFSG.LocalAnalysis.OddStandard.AltStdFormBigStdDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification
  CFSG.ComponentClassification.RestrictedStd.Spor

theorem altStdFormBigStd_holds :
    AltStdFormBigStd := by
  intro G _ _ L h n hn hθ
  have hS : StandardSetting G L := ⟨h.simple, h.nonabelian, h.kProper, h.standard⟩
  have hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := h.oddCore
  have hHN : HNLocalComponentsInput := hnLocalComponentsInput_holds
  have hFour : FourExactOuterInput :=
    fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput
  have hlookup : AltComponentLookup :=
    altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
      CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
      co1LocalComponentsInput_holds hHN hFour lyOuterTrivialInput
      Sporadic.FischerOddCore.fi22OuterComponentsInput_holds CatLeafProof.monsterInnerInput
      CatLeafProof.monsterLocalComponentsInput
  have htri : ExactShapeTrichotomy := exactShapeTrichotomy_holds
  have hR2 : RankTwoStandard.RankTwoAlternatingStandard :=
    RankTwoAlt.rankTwoAlternatingStandard_of_open
        (RankTwoAltFive.altFiveCaseI_of
            (RankTwoAlt.altGenerationFive_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA))
        (RankTwoAltFive.asc310EpsOne_of Asc76X.goldschmidtTheoremA) RankTwoAltFive.asc310IIb
        RankTwoAlt.altFiveM12NotTop_of RankTwoAlt.altEvenCenterSmall RankTwoAlt.altThreeCover
        (RankTwoAlt.altGenerationSmall_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA)
        RankTwoAlt.altRootFusion
        (RankTwoAlt.altTypeTwoFusion_of_rootFusion RankTwoAlt.altRootFusion)
        (RankTwoAlt.altTypeTwoCentralizer Asc76X.goldschmidtTheoremA)
  obtain ⟨S, hcyc⟩ := h.cyclicSylow
  rcases card_eq_two_or_four_le hS.standard.2.1 S with h2 | h4
  · by_cases hinner : ∀ z : G, z ∈ centralizer (L : Set G) → orderOf z = 2 →
        centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)
    · exact altStdBalancedOrder2Inner_ge_twelve hlookup hHN hFour G L hS n hn hθ S hcyc h2 hbal
        hinner
    · have hex : ∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧
          ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) := by
        push Not at hinner
        obtain ⟨z, hz, hz2, hzO⟩ := hinner
        exact ⟨z, hz, hz2, hzO⟩
      rcases Nat.lt_or_ge n 14 with h14 | h14
      · have hset : Setting G L n := ⟨hS, by omega, hθ, ⟨S, hcyc⟩, hbal⟩
        refine false_of_outer_of_shapeTwo hset S hcyc h2 hex fun Q z u d T => ?_
        obtain ⟨e⟩ := hθ
        rcases (show n = 12 ∨ n = 13 by omega) with rfl | rfl
        · exact false_of_shapeTwo_twelve htri shapeTwoCentDoubleAt_twelve_holds hset d T e
        · exact false_of_shapeTwo_thirteen htri hR2 hset d T e
      · exact altStdBalancedOrder2Outer_ge_fourteen htri
          (shapeTwoCaseIIClassification_of_rankTwo' htri hR2) G L hS n h14 hθ S hcyc h2 hbal hex
  · exact altStdBalancedBig_holds G L hS n (by omega) hθ S hcyc h4 hbal

end CFSG.OddStandard.AltStdSec
