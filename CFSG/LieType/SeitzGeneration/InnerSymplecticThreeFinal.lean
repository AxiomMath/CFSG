module

public import CFSG.LieType.SeitzGeneration.InnerSymplecticThreeAll
public import CFSG.LieType.SeitzGeneration.SpPlaneThreeF2

public section

namespace CFSG.LieType.SeitzGeneration

theorem spPlaneThreeF2Gen : SpPlaneThreeF2Gen := fun _ _ _ hK _ hr _ hcomm hexp hcard =>
  closure_centralizers_spPlane_three_F2 hK hr hcomm hexp hcard

theorem seitzInnerThreeSymplecticHigh : SeitzInnerThreeSymplecticHigh :=
  seitzInnerThreeSymplecticHigh_of_F2 spPlaneThreeF2Gen

end CFSG.LieType.SeitzGeneration
