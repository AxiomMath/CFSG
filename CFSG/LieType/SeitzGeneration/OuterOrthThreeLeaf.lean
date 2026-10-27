module

public import CFSG.LieType.SeitzGeneration.OuterOrthThree
public import CFSG.LieType.SeitzGeneration.ClassicalOuterLeaves

public section

namespace CFSG.LieType.SeitzGeneration

theorem seitzOuterOrthogonalThree : SeitzOuterOrthogonalThree :=
  seitzOuter_orthogonal_three subfieldPairOmegaThree_holds

end CFSG.LieType.SeitzGeneration
