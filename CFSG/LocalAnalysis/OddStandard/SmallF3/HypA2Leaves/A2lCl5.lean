module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

section


theorem chevThreeInter_holds : HypA2.ChevThreeInter := by
  intro S _ _ r _ hr2 hr3 h3 hr
  obtain ⟨τ, n, f, hτ⟩ := h3
  obtain ⟨τ', n', f', hτ'⟩ := hr
  exact absurd
    (ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds S τ n 3 f τ' n' r f'
      (by norm_num) hr2 hτ hτ').symm hr3

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
