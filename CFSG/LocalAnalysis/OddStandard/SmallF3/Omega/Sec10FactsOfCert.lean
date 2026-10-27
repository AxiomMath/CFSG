module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Fact1051
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Fact107c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Fact218
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactAutAb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactBCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCYCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCentB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCentK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCentZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactInvB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactK5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactN7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactOuterI4mCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactPockets
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactQ2m
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11FactAutQ
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Facts10_of_cert :
    Asc82Facts10 :=
  { sylow5 := asc82FactSylow5_of_cert
    out5 := asc82FactOut5_of_cert
    b5 := asc82FactB5_of_cert
    pockets5 := asc82FactPockets5_of_cert
    n7 := asc82FactN7_of_cert
    f1051 := asc82Fact1051_of_cert
    f107c := asc82Fact107c_of_cert
    f218c := asc82Fact218c_of_cert
    f218d := asc82Fact218d_of_cert
    f218e := asc82Fact218e_of_cert
    f218f := asc82Fact218f_of_cert
    centK5 := asc82FactCentK5_of_cert
    centZ5 := asc82FactCentZ5_of_cert
    centB5 := asc82FactCentB5_of_cert
    autAb := asc82FactAutAb_of_cert
    autK5 := asc82FactAutK5_of_struct
    outerI4m := asc82FactOuterI4m_of_cert
    factsC := asc82FactsC_of_cert
    factsB := ⟨asc82FactRankK5_of_struct, asc82FactQ2m_of_cert⟩
    ce16 := asc82FactCE16_of_cert
    invB := asc82FactInvB_of_cert
    autQ := asc82FactAutQ_of_cert }

end CFSG.OddStandard.SmallF3.Omega
