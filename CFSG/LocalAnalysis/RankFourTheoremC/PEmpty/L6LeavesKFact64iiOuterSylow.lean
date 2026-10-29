module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kFact64iiOuterSylow_of_reduced
    (h : CFSG.AGLEmbedding.OuterSylow.ReducedOuterSylow) : KFact64iiOuterSylow := by
  intro p hp hp3 K _ _ hsimple hnab hcat hrk φ hφ hφinn P
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hp2 : p ≠ 2 := by omega
  obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup K)
  rw [hrk, pow_one] at hEcard
  have hpK : p ∣ Nat.card K := by
    have hdvd := Subgroup.card_subgroup_dvd_card E
    rwa [hEcard] at hdvd
  have hcyc : IsCyclic (P : Subgroup K) := by
    refine CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2
      (le_top : (P : Subgroup K) ≤ ⊤) P.isPGroup' ?_
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact le_of_eq hrk
  have hφpow : φ ^ p = 1 := by
    rw [← hφ]
    exact pow_orderOf_eq_one φ
  by_contra hcon
  push Not at hcon
  exact hφinn (h K hsimple hnab hcat p hp hp2 hpK (P : Subgroup K) P.isPGroup'
    (Sylow.not_dvd_index P) hcyc φ hφpow hcon)

section Certified


theorem kFact64iiOuterSylow_holds : KFact64iiOuterSylow :=
  kFact64iiOuterSylow_of_reduced
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.reducedOuterSylow_holds

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
