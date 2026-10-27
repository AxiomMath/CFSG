module

public import CFSG.LieType.SeitzGeneration.RootPairOrthOdd
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlus
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinus

public section

namespace CFSG.LieType.SeitzGeneration

theorem subfieldPairOmega_of_char2
    (hP : SubfieldPairOmegaPlusChar2) (hM : SubfieldPairOmegaMinusChar2) : SubfieldPairOmega :=
  ⟨subfieldPairOmegaOdd, subfieldPairOmegaPlus_of_char2 hP, subfieldPairOmegaMinus_of_char2 hM⟩

end CFSG.LieType.SeitzGeneration
