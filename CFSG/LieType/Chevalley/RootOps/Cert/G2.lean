module

public import CFSG.LieType.Chevalley.RootOps.Cert.G2Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.G2Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.G2Conj0
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem g2_conjRange_all : conjRange .G2 0 12 = true := by
  have h0 : conjRange .G2 0 12 = true := g2_conjRange_0_12
  exact h0

theorem dataChecks_G2 : DataChecks .G2 := by
  refine dataChecks_of g2_tabCheck g2_allValid ?_ fun j => ?_
  · rw [Tag.rootCertificate_length]
    exact g2_conjRange_all
  · fin_cases j
    · exact g2_simpleRow_0
    · exact g2_simpleRow_1

end CFSG.LieType.Chevalley.RootOps
