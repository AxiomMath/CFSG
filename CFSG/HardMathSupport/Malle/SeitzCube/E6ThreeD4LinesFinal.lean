module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Lines
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open CFSG.LieType.SeitzGeneration


theorem e6ThreeD4Lines_proved (hgold : CFSG.Goldschmidt.TopStatement) : E6ThreeD4Lines :=
  e6ThreeD4Lines_of (fun _ hr => CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_one_proved hr)
    (fun _ hq => extSeitzAtInnerFor_trialityD4_even hgold hq)
    (fun _ hv _ => finite_isSimpleGroup_cat_trialityD4 hv)

end CFSG.HardMathSupport.Malle.SeitzCube
