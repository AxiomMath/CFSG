module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEnd175
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.RankTwoSporadic.Endgame

theorem sporadicCaseOdd_Ru_of_check
    (hY : YCensus (ruP.subgroupOf ruP) (Cert.ExcClass ruP ruE0Sub))
    (hE : RuEndFactsK)
    (hM : RuCentralTwoGroupOrderBound) (hW : RuDoubleCoverTwoBLift)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Ru := by
  intro G _ _ A hH hodd ⟨e⟩
  have hII : YCensus (ruP.subgroupOf ruP) (· ≤ ruP.subgroupOf ruP) := fun E _ _ h =>
    absurd (by rw [subgroupOf_self]; exact le_top) h
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus ruAutModel hII hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, hψ⟩ := exists_isActionHom ruAutModel hyp.standard.1.1 e
  obtain ⟨g, hg, RK, T, hR, hT, hTN, hRN, -, -, -⟩ :=
    AS76b.section3Config_of h32 h33 RankTwoFoundation.asc75Theorem4 AS76b.asc08Lemma34 G A hyp
  refine false_of_endgame h32 hyp le_rfl le_normalizer (fun x y => ?_) (ruEndFacts_of_K hE)
    hψ hY (fun _ ht2 htX hQ => odd_card_center hM hW h32 hyp e hψ ht2 htX hQ)
    hg hR hT hTN hRN
  rw [subgroupOf_self]
  exact mem_top _

end CFSG.ComponentClassification.RankTwoSporadic.Ru
