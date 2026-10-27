module

public import CFSG.LieType.Chevalley.RootOps.Cert.E6Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.E6Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.E6Conj0
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem e6_conjRange_all : conjRange .E6 0 72 = true := by
  have h0 : conjRange .E6 0 72 = true := e6_conjRange_0_72
  exact h0

theorem dataChecks_E6 : DataChecks .E6 := by
  refine dataChecks_of e6_tabCheck e6_allValid ?_ fun j => ?_
  · rw [Tag.rootCertificate_length]
    exact e6_conjRange_all
  · fin_cases j
    · exact e6_simpleRow_0
    · exact e6_simpleRow_1
    · exact e6_simpleRow_2
    · exact e6_simpleRow_3
    · exact e6_simpleRow_4
    · exact e6_simpleRow_5

end CFSG.LieType.Chevalley.RootOps
