module

public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.OpenExc

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LieType.SeitzGeneration

theorem excFiveResiduals_of_excParabolicPlane (h : ExcParabolicPlane) : ExcFiveResiduals where
  trialityOddFive := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  f4 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  e6 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  twistedE6 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  e7 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h
  e8 := ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1.not_classical) h

section KC


theorem stronglyEmbeddedPSL2KFact_proved : StronglyEmbeddedPSL2KFact :=
  stronglyEmbeddedPSL2KFact_of_excFiveResiduals
    (excFiveResiduals_of_excParabolicPlane CFSG.HardMathSupport.Malle.SeitzCube.excParabolicPlane_proved)

end KC

section YS


theorem ysPPointFrobenius_of_weak_proved
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointFrobenius :=
  ysPPointFrobenius_of_weak_exc hW
    (excFiveResiduals_of_excParabolicPlane CFSG.HardMathSupport.Malle.SeitzCube.excParabolicPlane_proved)

end YS

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
