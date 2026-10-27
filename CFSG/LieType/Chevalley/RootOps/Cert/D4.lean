module

public import CFSG.LieType.Chevalley.RootOps.Cert.D4Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.D4Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.D4Conj0
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem d4_conjRange_all : conjRange .D4 0 24 = true := by
  have h0 : conjRange .D4 0 24 = true := d4_conjRange_0_24
  exact h0

theorem dataChecks_D4 : DataChecks .D4 := by
  refine dataChecks_of d4_tabCheck d4_allValid ?_ fun j => ?_
  · rw [Tag.rootCertificate_length]
    exact d4_conjRange_all
  · fin_cases j
    · exact d4_simpleRow_0
    · exact d4_simpleRow_1
    · exact d4_simpleRow_2
    · exact d4_simpleRow_3

end CFSG.LieType.Chevalley.RootOps
