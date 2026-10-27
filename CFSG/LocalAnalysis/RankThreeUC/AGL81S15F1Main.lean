module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Fam

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

section Main

set_option linter.unusedSectionVars false


theorem kFactL32SimpleNormalizerAll_of_families
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    (h3o : F1L3Odd) (huo : F1U3Odd) : KFactL32SimpleNormalizerAll := by
  intro K _ _ hK hnab hcat hcyc A W Y hA hNW hYW hAY hY hWtop S hS' hSW
  obtain ⟨i, he⟩ := hcat
  have hr := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.pRank_three_eq_one_of_cyclic
    hcyc hA
  have key : F1For K := by
    rcases hS K hK hnab i he hr with
      ⟨d, (⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩), he'⟩ | he' | he'
    · exact f1L2_proved K d q hq hd he'
    · by_cases h2 : q.p = 2
      · exact f1L3Even_proved K d q h2 hq hd he'
      · exact h3o K d q h2 hq hd he'
    · by_cases h2 : q.p = 2
      · exact f1U3Even_proved K d q h2 hq hd he'
      · exact huo K d q h2 hq hd he'
    · exact f1J1_proved K he'
    · exact f1For_of_A5 K he'
  exact key hK hnab ⟨i, he⟩ hcyc A W Y hA hNW hYW hAY hY hWtop S hS' hSW

end Main

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
