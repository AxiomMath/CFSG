module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E7Cos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E8Lef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_stepI (F : Sec8T84Base) (hE : Asc82FinkE) (h89 : Asc82Lemma89)
    (h811 : Asc82Lemma811K) (hCos : Asc82OutCosets) : Asc82Step84IK := by
  intro G _ _ hK t L S z g B hctx
  rcases sec8t84_cos_cases F hCos h89 hctx with hleft | ⟨γ, hγS, hγ, hright⟩
  · exfalso
    obtain ⟨E, hEE⟩ := hE G t L S z g B hctx
    obtain ⟨Y1, Y2, hXO⟩ := h811 G hK t L S z g B E hEE
    exact sec8t84_left_false F h89 hEE hXO.core hleft
  · exact ⟨γ, hγS, hγ, hright⟩

end CFSG.OddStandard.SmallF3.Omega
