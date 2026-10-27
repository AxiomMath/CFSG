module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S3.KMFiveB

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem kmUsedAt_holds : KMUsedAt := by
  intro G _ _ p hp hp2 A T hA hT hAT hfaith hcard hbound
  have c : S3.KM.Ctx p A T := ⟨hp, hp2, hA, hT, hAT, hfaith, hcard, hbound⟩
  have h5 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    by_cases h3 : p = 3
    · exact Or.inl h3
    · right
      by_contra h
      have h4 : p = 4 := by omega
      rw [h4] at hp
      exact absurd hp (by norm_num)
  rcases h5 with hp3 | hp5
  · refine ⟨⟨hT, ?_⟩, hp3⟩
    exact c.isCyclic_of_three hp3 (c.exists_centralizer_ne_one_of_three hp3)
  · exact (c.false_of_five hp5).elim

end CFSG.LocalAnalysis.GLTheoremA
