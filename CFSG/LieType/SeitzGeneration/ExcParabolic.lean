module

public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LieType.SeitzGeneration.ExcParabolicTw
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeG2
public import CFSG.LieType.SeitzGeneration.ExcParabolicSuzuki
public import CFSG.LieType.SeitzGeneration.ExcParabolicTits

public section

namespace CFSG.LieType.SeitzGeneration

section Ree


theorem seitzExcParabolicRee : SeitzExcParabolicRee :=
  seitzExcParabolicRee_of_parts seitzExcParabolicFor_suzuki seitzExcParabolicFor_reeG2
    seitzExcParabolicFor_reeF4 seitzExcParabolicFor_tits

end Ree

section All


theorem seitzExcParabolic : SeitzExcParabolic :=
  seitzExcParabolic_of_parts (seitzExcParabolicChev_of_parts seitzExcParabolicUntw
    seitzExcParabolicTw) seitzExcParabolicRee

end All

end CFSG.LieType.SeitzGeneration
