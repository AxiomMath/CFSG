module

public import CFSG.GF2Type.Smith1979.W4AsSurvL28
public import CFSG.GF2Type.Smith1979.W4AsSurvL216
public import CFSG.GF2Type.Smith1979.W4AsSurvJ1
public import CFSG.GF2Type.Smith1979.W4AsSurvRee

public section

namespace CFSG.GF2Type.Smith1979.W4As

theorem layerSurvivorsW4_holds : LayerSurvivorsW4 :=
  ⟨l28NoSmallFaithful_holds, l216NoPlusEmbedding_holds, j1NoFaithfulEight_holds,
    reeNoFaithfulEight_holds⟩

end CFSG.GF2Type.Smith1979.W4As
