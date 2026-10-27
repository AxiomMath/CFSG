module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFactKlingenSylowNormalCyclic_holds : KFactKlingenSylowNormalCyclic := by
  intro p _ hp2 d hd K _ _ hK T N hN hT hc
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := hK
  by_cases hp3 : p = 3
  · subst hp3
    exact kFactKlingenSylowNormalCyclic_three d hd K e T N hN hT hc
  · have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have h2 := hp.two_le
    exact kFactKlingenSylowNormalCyclic_of_five_le p (by omega) d hd K ⟨e⟩ T N hN hT hc

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
