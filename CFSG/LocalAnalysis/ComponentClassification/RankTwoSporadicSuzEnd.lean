module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEnd175
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCensusW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndModel

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.RankTwoSporadic.Endgame
open scoped commutatorElement

theorem suzCommutator_mem
    (x y : ↥suzT) : ⁅x, y⁆ ∈ suzM.subgroupOf suzT := by
  have h2 := suzM_index_T
  rw [commutatorElement_def, mul_mem_iff_of_index_two h2, mul_mem_iff_of_index_two h2,
    mul_mem_iff_of_index_two h2, inv_mem_iff, inv_mem_iff]
  tauto

theorem sporadicCaseOdd_Suz_of_check
    {d d' : CFSG.KC.Census.ConjDataP} (hII : suzCheckWII d = true)
    (hX : suzCheckWExc suzE0 d' = true)
    (hE : SuzEndFactsK)
    (hM : SuzCentralTwoGroupOrderBound) (hW : SuzDoubleCoverTwoBLift)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Suz := by
  intro G _ _ A hH hodd ⟨e⟩
  obtain ⟨hyp, -⟩ := suz_exc_of_checkW hII hX h32 h33 hH hodd e
  obtain ⟨ψ, hψ⟩ := exists_isActionHom suzAutModel hyp.standard.1.1 e
  obtain ⟨g, hg, RK, T, hR, hT, hTN, hRN, -, -, -⟩ :=
    AS76b.section3Config_of h32 h33 RankTwoFoundation.asc75Theorem4 AS76b.asc08Lemma34 G A hyp
  exact false_of_endgame h32 hyp suzM_le_suzT
    ((normal_subgroupOf_iff_le_normalizer suzM_le_suzT).1 suzM_normal_T) suzCommutator_mem
    (suzEndFacts_of_K hE) hψ (suz_yCensusExcW hX)
    (fun _ ht2 htX hQ => odd_card_center hM hW h32 hyp e hψ ht2 htX hQ) hg hR hT hTN hRN

end CFSG.ComponentClassification.RankTwoSporadic.Suz
