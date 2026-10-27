module

public import CFSG.LieType.SeitzGeneration.ClassicalSeitzStatus
public import CFSG.LieType.SeitzGeneration.ExcSeitzStatus

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2


theorem seitzOuterLowN_holds : SeitzOuterLowN := by
  intro d p hp hp2 hpd hex E hE hc ⟨hout, hs⟩
  by_cases hcl : IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)
  · exact seitzOuterClassical_holds d p hp hp2 hpd hex E hE hc ⟨hout, hcl.1, hcl.2⟩
  · by_cases h1 : IsClassicalIndex d.1
    · have h2 : p = 3 ∧ IsDFourIndex d.1 := by
        by_contra h2
        exact hcl ⟨h1, h2⟩
      exact seitzOuter_dFour_three d p hp hp2 hpd hex E hE hc ⟨hout, hs, h2.1, h2.2⟩
    · exact seitzExcOuterNarrow_holds d p hp hp2 hpd hex E hE hc ⟨hout, hs, h1⟩

end CFSG.LieType.SeitzGeneration
