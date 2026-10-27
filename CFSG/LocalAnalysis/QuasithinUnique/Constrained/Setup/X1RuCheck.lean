module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.Ru.Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuCheckInputs
public import Certificates.Certificate4061

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Th.Native (ap)
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_progValid : slpValidAux ruProg2 2 = true :=
  Certificates.certificate4061.1

theorem ru_wprogValid : slpValidAux ruWprog 2 = true :=
  Certificates.certificate4061.2.1

theorem ru_qpOK : qpOK ruData.n ruNT2 ruQp :=
  Certificates.certificate4061.2.2.1

theorem ru_enumOK :
    BaseEnumOK ruData.n ruB' ruGens2 ruGensI2 ruEnum2.1 ruEnum2.2.1
    ruEnum2.2.2 :=
  Certificates.certificate4061.2.2.2.1

theorem ru_enum_size : ruEnum2.1.size = 2 ^ 14 :=
  Certificates.certificate4061.2.2.2.2.1

theorem ru_bounds :
    ruGn < ruNT2.size ∧ ruGin < ruNT2.size ∧ ruHn < ruNT2.size ∧
    ruHin < ruNT2.size ∧ ruAn < ruWNT.size ∧ ruBn < ruWNT.size :=
  Certificates.certificate4061.2.2.2.2.2.1

theorem ru_nodes :
    nodesLt ruNT2.size ruNodes1 = true ∧ nodesLt ruNT2.size ruNodes2 = true ∧
    nodesLt ruNT2.size ruNodes3 = true :=
  Certificates.certificate4061.2.2.2.2.2.2.1

theorem ru_c1 :
    zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 [Array.range ruData.n] ruL1 = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.1

theorem ru_c2 :
    zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 ruL1 ruL2 = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.1

theorem ru_c3 :
    zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 ruL2 ruL3 = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.1

theorem ru_gg :
    invPairOK (Array.range ruData.n) ruNT2[ruGn]! ruNT2[ruGin]! = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.1

theorem ru_hh :
    invPairOK (Array.range ruData.n) ruNT2[ruHn]! ruNT2[ruHin]! = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.1

theorem ru_normZ1 : normOK ruL1 ruNT2[ruGn]! ruNT2[ruGin]! = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ru_normZ3 : normOK ruL3 ruNT2[ruHn]! ruNT2[ruHin]! = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ru_notNormZ3 :
    notNormOK ruL3 ruNT2[ruGn]! ruNT2[ruGin]! = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ru_notNormZ1 :
    notNormOK ruL1 ruNT2[ruHn]! ruNT2[ruHin]! = true :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ru_wa : ruWNT[ruAn]! = ruTa' :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ru_wb : ruWNT[ruBn]! = ruTb' :=
  Certificates.certificate4061.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.Setup.X1
