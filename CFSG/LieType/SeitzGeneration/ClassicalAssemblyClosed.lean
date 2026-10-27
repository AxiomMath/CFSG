module

public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyRestFour
public import CFSG.LieType.SeitzGeneration.RegimesLowNarrow
public import CFSG.LieType.SeitzGeneration.UnitaryToralNine
public import CFSG.LieType.SeitzGeneration.OrthDfourBig

public section

namespace CFSG.LieType.SeitzGeneration

theorem innerExFor_classical_of_heisCore (hcore : UnitaryHeisCore) :
    InnerExFor fun d => IsClassicalIndex d.1 :=
  innerExFor_classical'' hcore unitaryToralNine
    (orthSelfDualRestFour_of_restD4 orthSelfDualRestD4)

theorem seitzInnerLowClassical_of_heisCore (hcore : UnitaryHeisCore) : SeitzInnerLowClassical :=
  seitzInnerLowClassical'' hcore unitaryToralNine
    (orthSelfDualRestFour_of_restD4 orthSelfDualRestD4)

theorem innerEx_lowN_of_heisCore (hcore : UnitaryHeisCore) (hCON : SeitzOuterLowNarrow)
    (hPar : SeitzExcParabolic) (hParEx : ExcParabolicPlane) (hAni : SeitzExcAnisotropic)
    (hXON : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1))) :
    KFactSeitzRankTwoInnerEx ∧ KFactSeitzRankTwoLowN :=
  innerEx_lowN_of_regimes (innerExFor_classical_of_heisCore hcore)
    (seitzInnerLowClassical_of_heisCore hcore) hCON hPar hParEx hAni hXON

end CFSG.LieType.SeitzGeneration
