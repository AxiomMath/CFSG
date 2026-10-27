module

public import CFSG.CGT.T75JM.PCheck
public import Certificates.Certificate14983

public section

namespace CFSG.CGT.T75JM

theorem pFacts_of_certificate :
    PFacts := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Certificates.certificate14983
  exact pFacts_of_checks h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem pStatement_of_certificate :
    PStatement :=
  pStatement_of_facts pFacts_of_certificate

end CFSG.CGT.T75JM
