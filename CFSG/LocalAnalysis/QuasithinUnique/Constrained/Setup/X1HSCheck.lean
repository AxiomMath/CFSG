module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.HS.Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSCheckInputs
public import Certificates.Certificate4133

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Th.Native (ap)
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_progValid : slpValidAux hsProg2 2 = true :=
  Certificates.certificate4133.1

theorem hs_wprogValid : slpValidAux hsWprog 2 = true :=
  Certificates.certificate4133.2.1

theorem hs_qpOK : qpOK hsData.n hsNT2 hsQp :=
  Certificates.certificate4133.2.2.1

theorem hs_enumOK :
    BaseEnumOK hsData.n (List.range hsData.n) hsGens2 hsGensI2 hsEnum2.1
    hsEnum2.2.1 hsEnum2.2.2 :=
  Certificates.certificate4133.2.2.2.1

theorem hs_enum_size : hsEnum2.1.size = 2 ^ 9 :=
  Certificates.certificate4133.2.2.2.2.1

theorem hs_bounds :
    hsGn < hsNT2.size ∧ hsGin < hsNT2.size ∧ hsHn < hsNT2.size ∧
    hsHin < hsNT2.size ∧ hsAn < hsWNT.size ∧ hsBn < hsWNT.size :=
  Certificates.certificate4133.2.2.2.2.2.1

theorem hs_gg :
    invPairOK (Array.range hsData.n) hsNT2[hsGn]! hsNT2[hsGin]! = true :=
  Certificates.certificate4133.2.2.2.2.2.2.1

theorem hs_hh :
    invPairOK (Array.range hsData.n) hsNT2[hsHn]! hsNT2[hsHin]! = true :=
  Certificates.certificate4133.2.2.2.2.2.2.2.1

theorem hs_normZ1 : normOK hsZ1 hsNT2[hsGn]! hsNT2[hsGin]! = true :=
  Certificates.certificate4133.2.2.2.2.2.2.2.2.1

theorem hs_normQc : normOK hsQc hsNT2[hsHn]! hsNT2[hsHin]! = true :=
  Certificates.certificate4133.2.2.2.2.2.2.2.2.2.1

theorem hs_notNormQc :
    notNormOK hsQc hsNT2[hsGn]! hsNT2[hsGin]! = true :=
  Certificates.certificate4133.2.2.2.2.2.2.2.2.2.2.1

theorem hs_notNormZ1 :
    notNormOK hsZ1 hsNT2[hsHn]! hsNT2[hsHin]! = true :=
  Certificates.certificate4133.2.2.2.2.2.2.2.2.2.2.2.1

theorem hs_wa : hsWNT[hsAn]! = hsTa' :=
  Certificates.certificate4133.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hs_wb : hsWNT[hsBn]! = hsTb' :=
  Certificates.certificate4133.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.Setup.X1
