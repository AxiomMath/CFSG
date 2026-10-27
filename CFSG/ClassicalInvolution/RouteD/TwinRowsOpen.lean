module

public import CFSG.ClassicalInvolution.RouteD.TWEClose
public import CFSG.ClassicalInvolution.RouteD.TWEB6Main
public import CFSG.ClassicalInvolution.RouteD.TWS6D4Rank
public import CFSG.ClassicalInvolution.RouteD.TWS6Cfg
public import CFSG.ClassicalInvolution.RouteD.TWEAssemble
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
public import CFSG.ClassicalInvolution.RouteD.TWS6SRow

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

variable (p f : ℕ) [Fact p.Prime]

structure TwinVisNCOpen : Prop where
  visB3 : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3
  ncB3 : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3
  visTD4 : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4
  ncTD4 : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4

end CFSG.ClassicalInvolution.RouteD.TwinY
