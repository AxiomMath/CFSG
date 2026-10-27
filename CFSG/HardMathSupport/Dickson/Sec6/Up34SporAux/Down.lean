module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.Reduction
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.HardMathSupport.Solomon.Coordinator

theorem sporL34Free_of_down {s : TauCeti.SporadicName} (h : YS08.SporL3DownInner s) :
    SporL34Free s := by
  intro S _ _ hS hnab he g hg I hcfg
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  exact h S hS hnab he g hg3 I hcfg.1 2 (YS08.isL3Kind_of_isLThreeFour hcfg.2)

end CFSG.HardMathSupport.Dickson.Sec6
