module

public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyCores
public import CFSG.LieType.SeitzGeneration.OrthRestFour

public section

namespace CFSG.LieType.SeitzGeneration

theorem innerExFor_classical'' (hcore : UnitaryHeisCore) (htoral : UnitaryToralNine)
    (hO : OrthSelfDualRestFour) : InnerExFor fun d => IsClassicalIndex d.1 :=
  innerExFor_classical' hcore htoral (orthSelfDualTwoBlocks_of_restFour hO)

theorem seitzInnerLowClassical'' (hcore : UnitaryHeisCore) (htoral : UnitaryToralNine)
    (hO : OrthSelfDualRestFour) : SeitzInnerLowClassical :=
  seitzInnerLowClassical' hcore htoral (orthSelfDualTwoBlocks_of_restFour hO)

end CFSG.LieType.SeitzGeneration
