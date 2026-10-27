module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44Main
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsExtend

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

theorem l44Input : YamadaEnd.L44Input :=
  l44Input_of_extend fun _ _ _ _ hF θ => exists_extend_msigma hF θ

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
