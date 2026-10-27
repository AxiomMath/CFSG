module

public import CFSG.LieType.SeitzGeneration.InnerSymplecticThreeFinal
public import CFSG.LieType.SeitzGeneration.OrthManyThree
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeLeaf
public import CFSG.LieType.SeitzGeneration.OutdiagParabolic
public import CFSG.LieType.SeitzGeneration.OuterUnitaryEight
public import CFSG.LieType.SeitzGeneration.UnitaryTwoNonCubeAll
public import CFSG.LieType.SeitzGeneration.SingerTorusLinear
public import CFSG.LieType.SeitzGeneration.SingerUMain

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

section Status

theorem seitzInnerThreeClassical_of_orderNine (h9 : UnitaryTwoOrderNinePlanes) :
    SeitzInnerThreeClassical :=
  seitzInnerThreeClassical_of_leaves (seitzInnerThreeUnitaryTwo_of unitaryHeisTensorPlanes_holds h9)
    seitzInnerThreeUnitaryNonabHigh seitzInnerThreeSymplecticHigh seitzInnerThreeOrthogonal

theorem seitzInnerThreeClassical_holds : SeitzInnerThreeClassical :=
  seitzInnerThreeClassical_of_orderNine unitaryTwoOrderNinePlanes_holds

theorem seitzOuterClassical_of_open (hR : OutdiagReduciblePlanes) (hH : OutdiagHeisenbergPlanes)
    (h8 : UnitaryOuterEightPlanes) (hH5 : UnitaryOuterHeisFive) (hA2 : UnitaryOuterAbTwo)
    (hA5 : UnitaryOuterAbFive) : SeitzOuterClassical :=
  seitzOuterClassical_of_leaves subfieldPairOmegaPlusF2_holds subfieldPairOmegaMinusF2_holds
    (seitzOuterLinearWide_of_outdiag hR hH)
    (seitzOuterUnitaryWide_of h8 unitaryOuterHeisThree hH5 hA2 hA5) seitzOuterOrthogonalThree

theorem seitzOuterClassical_holds : SeitzOuterClassical :=
  seitzOuterClassical_of_open outdiagReduciblePlanes_holds outdiagHeisenbergPlanes_holds
    unitaryOuterEightPlanes unitaryOuterHeisFive_holds unitaryOuterAbTwo_holds
    unitaryOuterAbFive_holds

end Status

end CFSG.LieType.SeitzGeneration
