module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuz
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.KC.Census

theorem suz_yCensusIIW
    {d : ConjDataP} (h : suzCheckWII d = true) :
    YCensus (suzM.subgroupOf suzT) (· ≤ suzM.subgroupOf suzT) := by
  simp only [suzCheckWII, suzXsOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, hgen, hlen⟩ := h
  exact yCensusII_pair_conjW (m := 54729675) suzM_le_suzT suzM_normal_T suzPS_lt suzInM_iff
    rep_v suzV_mem_suzT hc hgen (by rw [hlen, suzT_card]; norm_num) (by decide)

theorem suz_yCensusExcW
    {d : ConjDataP} (h : suzCheckWExc suzE0 d = true) :
    YCensus (suzM.subgroupOf suzT) (ExcClass suzT suzE0Sub) := by
  simp only [suzCheckWExc, suzXsOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, hgen, hlen⟩ := h
  exact yCensusExc_pair_conjW (m := 54729675) suzM_le_suzT suzM_normal_T suzPS_lt suzInM_iff
    rep_v suzV_mem_suzT hc hgen (by rw [hlen, suzT_card]; norm_num) (by decide)

theorem suz_exc_of_checkW
    {d d' : ConjDataP} (hII : suzCheckWII d = true)
    (hX : suzCheckWExc suzE0 d' = true) (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hH : RankTwoStandard.RankTwoHyp G A)
    (hodd : standardComponentOddCore G = ⊥)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .Suz) :
    AS76b.Hyp31 A ∧ ∃ ψ : normalizer (A : Set G) →* ↥suzT, IsActionHom A (suzM.subgroupOf suzT) ψ ∧
      ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) ∧
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
        ExcClass suzT suzE0Sub ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus suzAutModel (suz_yCensusIIW hII) hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, hψ, g, hg, T, hT1, hT2, hExc⟩ := exc_of_yCensus h32 h33 hyp suzAutModel e
  exact ⟨hyp, ψ, hψ, g, hg, T, hT1, hT2, hExc _ (suz_yCensusExcW hX)⟩

end CFSG.ComponentClassification.RankTwoSporadic.Suz
