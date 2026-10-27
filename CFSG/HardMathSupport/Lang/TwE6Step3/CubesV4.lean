module

public import CFSG.HardMathSupport.Lang.TwE6Step3.SixFinal
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Frontier
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4LinesFinal
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.E7SixProved

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)


set_option linter.unusedSectionVars false


theorem excCubeResidualsV4_of_phi6 (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) :
    CFSG.LieType.SeitzGeneration.ExcCubeResidualsV4 :=
  CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.excCubeResidualsV4_of_frontiers
    (CFSG.HardMathSupport.Malle.SeitzCube.e6ThreeD4Lines_proved CFSG.Goldschmidt.topStatement)
    (twE6SixLines_of_phi6 h6) CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.e7SixStep3Adj_proved

end CFSG.HardMathSupport.Lang.TwE6Step3
