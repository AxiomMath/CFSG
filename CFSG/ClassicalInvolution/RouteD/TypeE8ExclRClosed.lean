module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclRFinal
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerPsi
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

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

variable {p f : ℕ} [Fact p.Prime]

theorem e8ClassExcluded_of_three (hConn : p ≠ 2 → 5 ≤ p ^ f → Fund12Connected p f)
    (hRow : E8D8Row' p f) (hD8 : E8D8NoThreeAdj p f) : E8ClassExcluded p f := by
  intro G _ _ _ hnab K z S hshape c β hβ t htβ hKβ ht g p₀ hT
  exact e8ClassExcluded (ModelFacts.E7Model.e7LayerEquiv S.odd S.five) (hConn S.odd S.five)
    hRow hD8 G hnab K z S hshape c β hβ t htβ hKβ ht g p₀ hT

end CFSG.ClassicalInvolution.RouteD.TypeE8
