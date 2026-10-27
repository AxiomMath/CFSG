module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternWired
public import CFSG.ClassicalInvolution.RouteD.TypeE8TorGlue
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate121
public import Certificates.Certificate122
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem e8TorusFixed_of_model (hB1 : TypeE8.E7PairFrame p f) (hB5 : TypeE8.E7TorusFixedModel p f) :
    E8TorusFixed p f := by
  intro G _ _ _ _ K z _ hshape c j hj hjimg β hβ t htβ hKβ hβ0 ht
  exact c.torusFixedE7_of_node_system hB1 hB5 (single_class K) hshape hj hjimg hβ htβ hKβ hβ0 ht

theorem e8TorusFixed_of_frame_toral (hB1 : TypeE8.E7PairFrame p f) (hF : TypeE8.E7A1A4Frame p f)
    (hT : TypeE8.E7A1A4Toral p f) : E8TorusFixed p f :=
  e8TorusFixed_of_model hB1 (TypeE8.e7TorusFixedModel_of_frame_toral p f hF hT)

end CFSG.ClassicalInvolution.MilestoneAssembly
