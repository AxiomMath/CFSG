module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridge
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALayer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz3D48Proof

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ


theorem seitz3D48Cube_holds : Seitz3D48Cube := by
  intro S _ _ _ _ d q hq hd he E hE hcard
  obtain ⟨d₀, hv⟩ := d
  simp only at hd
  subst hd
  exact CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer q hv hq.1
    (by rw [hq.2]; norm_num) S he E hE (by rw [hcard]; norm_num)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz3D48Proof
