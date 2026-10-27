module

public import CFSG.LieType.SeitzGeneration.ClassicalAssembly
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitaryScope

public section

namespace CFSG.LieType.SeitzGeneration

theorem seitzInnerUnitaryThreeNonab_of_cores (hcore : UnitaryHeisCore)
    (htoral : UnitaryToralNine) : SeitzInnerUnitaryThreeNonab :=
  seitzInnerUnitaryNonab hcore htoral

theorem innerExFor_classical' (hcore : UnitaryHeisCore) (htoral : UnitaryToralNine)
    (hO : OrthSelfDualTwoBlocks) : InnerExFor fun d => IsClassicalIndex d.1 :=
  innerExFor_classical (seitzInnerUnitaryThreeNonab_of_cores hcore htoral) hO

theorem seitzInnerLowClassical' (hcore : UnitaryHeisCore) (htoral : UnitaryToralNine)
    (hO : OrthSelfDualTwoBlocks) : SeitzInnerLowClassical :=
  seitzInnerLowClassical (seitzInnerUnitaryThreeNonab_of_cores hcore htoral) hO

end CFSG.LieType.SeitzGeneration
