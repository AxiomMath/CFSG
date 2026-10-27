module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactsCInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCSwCert

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactsC_of_cy
    (hy : Asc82FactCY) :
    Asc82FactsC :=
  ⟨asc82FactCTy_of_cert, asc82FactCSw_of_cert, asc82FactCLay_of_cert, asc82FactCI2p_of_cert,
    asc82FactCI2m_of_cert, hy⟩

end CFSG.OddStandard.SmallF3.Omega
