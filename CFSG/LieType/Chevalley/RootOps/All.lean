module

public import CFSG.LieType.Chevalley.RootOps.Cert.G2
public import CFSG.LieType.Chevalley.RootOps.Cert.F4
public import CFSG.LieType.Chevalley.RootOps.Cert.D4
public import CFSG.LieType.Chevalley.RootOps.Cert.E6
public import CFSG.LieType.Chevalley.RootOps.Cert.E7
public import CFSG.LieType.Chevalley.RootOps.Cert.E8
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem RootOps.dataChecks : ∀ τ : Tag, RootOps.DataChecks τ
  | .G2 => RootOps.dataChecks_G2
  | .F4 => RootOps.dataChecks_F4
  | .D4 => RootOps.dataChecks_D4
  | .E6 => RootOps.dataChecks_E6
  | .E7 => RootOps.dataChecks_E7
  | .E8 => RootOps.dataChecks_E8

@[expose] noncomputable def rootOperatorFamily (τ : Tag) : RootOperatorFamily τ :=
  (RootOps.dataChecks τ).family

end CFSG.LieType.Chevalley
