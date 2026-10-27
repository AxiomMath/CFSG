module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434DefPSL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434DefExc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.Blueprint (LieModel)

theorem i1434DefCase_holds
    : I1434DefCase := by
  intro K _ _ t n f hadm hM Q x J₁ J₂ hD
  rcases hM with ⟨ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩
  · by_cases h2 : t = .PSL ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := h2
      exact I1434.psl2_five_false hm hD
    · exact I1434.classical_five_false hm h2 hD
  · exact I1434.chevalley_five_false hm hD
  · exfalso
    obtain ⟨hadm', -⟩ := hm
    simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> simp [StatedLieAdmissible] at hadm'
  · exfalso
    obtain ⟨hp, -⟩ := hm
    exact absurd hp (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
