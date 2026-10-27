module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearAssembly
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEndingMain
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section RankOne

theorem seitzRankOneExclusion_of_final (hM : RankOne.GMS43MasonInput)
    (hU : RankOne.RankOneUnitaryExclusion) (hC1 : RankOne.SzC1ExclusionData) :
    SeitzRankOneExclusion :=
  RankOne.seitzRankOneExclusion_of_kernel RankOne.rankOneKernel
    (RankOne.rankOneLinearExclusion_of_gms43 (RankOne.gms43InvolutionCase_of_masonInput hM)) hU
    (RankOne.rankOneSuzukiExclusion_of_c1Data hC1)

end RankOne

end CFSG.SeitzReduction
