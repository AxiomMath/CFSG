module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Con
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Dec

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FinkE_of (F : Sec8T84Base) (hKL : Sec8T84KL1) (hQ : Sec8T84FactQuad)
    (hL : Sec8T84FactLift) (hA5 : Sec8T84FactA5) : Asc82FinkE := by
  intro G _ _ t L S z g B hctx
  obtain ⟨K, L1, h⟩ := hKL G t L S z g B hctx
  refine ⟨L1, ?_⟩
  rcases A3.dich F hQ hctx h with h1 | h2
  · exact A3.sec8E_of_sq F hctx h h1
  · exact (A3.case2_false F hA5 hL hctx h h2).elim

end CFSG.OddStandard.SmallF3.Omega
