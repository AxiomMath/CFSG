module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalIn30_2
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalEps

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem lemma27_input30_2_holds : Lemma27Ns.Input30_2 := by
  intro X _ _ hε
  obtain ⟨π, p, f, K, _, φ, hK, hq, hφ⟩ := l3b_model_of_isSL3Eps hε
  exact ⟨l3b_P1 hK hq hφ, fun hsyl P => l3b_P2 hK hq hφ hsyl P,
    fun x hx3 hP => l3b_P3 hK hq hφ x hx3 hP⟩

end CFSG.HardMathSupport.Solomon.Coordinator
