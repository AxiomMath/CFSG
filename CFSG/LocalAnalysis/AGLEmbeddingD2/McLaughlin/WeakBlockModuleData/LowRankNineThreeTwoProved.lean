module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CensusRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicOvergroup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem kFactLowRankNineThreeTwo_proved : KFactLowRankNineThreeTwo := by
  intro G _ _ M S L hL h932 hnS hsolv hr hZ
  obtain ⟨hY, hpar, hS⟩ := h932
  have hnot : ¬ IsSylowTwoOf (pCoreOf 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
      (barM M L) := hS ▸ hnS
  obtain ⟨T, J, hT, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient _ _ hpar hnot hsolv
  have hrq := pRank_top_quot_center_eq hL.le hZ
  rcases kFactParabolicThreeCensus _ hY T J hT hNJ hJne hJperf with
    ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩, ⟨e⟩⟩
  · exfalso
    have h2 := two_le_pRank_of_classicalIndexTwo d hd e
    omega
  · exfalso
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
      hrq
    rcases hn with rfl | rfl | rfl
    · exact a5_overgroup_false e T J hT hNJ hJne hJperf
    · have := two_le_pRank_alternatingGroup_six
      omega
    · have := le_pRank_alternatingGroup_three (N := 8) (k := 2) (by norm_num)
      omega
  · exact ⟨d, ⟨q, hq, hd1⟩, ⟨e⟩⟩
  · exfalso
    have h2 := (u33FactsExact_proved _ ⟨d, ⟨q, hq, hd1⟩, ⟨e⟩⟩).2
    omega

end CFSG.AGLEmbeddingD2.McLaughlin
