module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalTw
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedE6Frame
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBoot
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinal
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Assembly.LowTwoRank

theorem layerGenerationHybrid (p : ℕ) [Fact p.Prime] : LayerGenerationHybrid p :=
  layerGenerationHybrid_of_pairFrames
    (fun t e _ ht hp2 _ hadm => by
      rcases ht with rfl | rfl | rfl | rfl
      · exact ModelFacts.pairFrame_e6 hp2 hadm
      · exact ModelFacts.pairFrame_e7 hp2 hadm
      · exact ModelFacts.pairFrame_e8 hp2 hadm
      · exact ModelFacts.pairFrame_f4 hp2 hadm)
    (fun _ _ hadm hp2 _ => twistedE6_pairFrame hadm hp2)

end CFSG.ClassicalInvolution.Balance.Bootstrap
