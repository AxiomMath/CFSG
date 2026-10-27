module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGPerf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSol

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup

section Certified

theorem knownRowThree_holds (hCI : GSLit.ClassicalInvolutionInput)
    (h51 : Harris82Lemma51Quat) : KnownRowThree := by
  intro G _ _ hY hcat z hz L hL hzL hI
  rcases hL with hLp | hLs
  · have hT : PerfType3 ↥L := by
      rcases hI with hI | ⟨-, hlie | ⟨⟨e⟩⟩⟩
      · exact .inl hI
      · exact .inr hlie
      · exact (false_of_isQuasisimple_of_sl2Three hLp.2.2.2 (.inr ⟨e⟩)).elim
    exact knownRowThree_perfect hY hcat hz hLp hzL hT
  · rcases hI with ⟨f, hf, h⟩ | ⟨-, ⟨τ, n, hm⟩ | ⟨⟨e⟩⟩⟩
    · exfalso
      have hQ : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := by
        rcases h with h | h | h | h | ⟨hev, hsl⟩
        · exact h.1
        · exact h.1
        · exact h.1
        · exact h.1
        · have hf2 : 2 ≤ f := by
            obtain ⟨k, hk⟩ := hev
            omega
          have h5 : 5 ≤ 3 ^ f :=
            le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hf2)
          exact (Lemma47.sl2_facts Nat.prime_three (by norm_num) hf h5 hsl).1
      exact false_of_isQuasisimple_of_sl2Three hQ hLs.2.2.2
    · exact (false_of_lieModel_three_of_card_dvd hm (card_fusionZStar_dvd hLs.2.2.2)).elim
    · exact knownRowThree_solvable hCI h51 hY hz hLs hzL e

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
