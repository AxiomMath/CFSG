module

public import CFSG.LieType.SeitzGeneration.HyperExCubeUntw

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley TauCeti CFSG.Open CFSG.AGLEmbedding

structure ExcCubeResidualsV2 : Prop where
  e6High : ExcCubeHigh .E6 LieTypeIndex.E6
  e7High : ExcCubeHigh .E7 LieTypeIndex.E7
  e8High : ExcCubeHigh .E8 LieTypeIndex.E8
  twistedE6 : ExcCubeFor IsTwistedE6Index

theorem ExcCubeResidualsV2.toResiduals (h : ExcCubeResidualsV2) : ExcCubeResiduals where
  g2 := excCubeFor_G2
  f4 := excCubeFor_F4
  e6 := excCubeFor_E6_of_high h.e6High
  e7 := excCubeFor_E7_of_high h.e7High
  e8 := excCubeFor_E8_of_high h.e8High
  triality := excCubeFor_triality
  twistedE6 := h.twistedE6
  reeTypeThree := hyperExReeTypeThree

end CFSG.LieType.SeitzGeneration
