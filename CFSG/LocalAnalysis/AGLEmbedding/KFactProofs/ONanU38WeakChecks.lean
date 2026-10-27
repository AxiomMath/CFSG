module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38S1Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38P1Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Y9Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Model
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Y9

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

theorem checkE_s1 : checkE s1Sc validS s1Data = true := by decide +kernel

theorem checkG_s1_zero : checkG s1Sc validS s1Data 0 = true := by decide +kernel

theorem checkG_s1_one : checkG s1Sc validS s1Data 1 = true := by decide +kernel

theorem checkE_p1 : checkE p1Sc validS p1Data = true := by decide +kernel

theorem checkG_p1_zero : checkG p1Sc validS p1Data 0 = true := by decide +kernel

theorem checkG_p1_one : checkG p1Sc validS p1Data 1 = true := by decide +kernel

theorem checkE_y9 : checkE y9Sc valid9 y9Data = true := by decide +kernel

theorem checkG_y9_zero : checkG y9Sc valid9 y9Data 0 = true := by decide +kernel

theorem checkG_y9_one : checkG y9Sc valid9 y9Data 1 = true := by decide +kernel

end CFSG.AGLEmbedding.ChevOuter.U38
