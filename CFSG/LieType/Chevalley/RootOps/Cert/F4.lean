module

public import CFSG.LieType.Chevalley.RootOps.Cert.F4Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.F4Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.F4Conj0
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem f4_conjRange_all : conjRange .F4 0 48 = true := by
  have h0 : conjRange .F4 0 48 = true := f4_conjRange_0_48
  exact h0

theorem dataChecks_F4 : DataChecks .F4 := by
  refine dataChecks_of f4_tabCheck f4_allValid ?_ fun j => ?_
  · rw [Tag.rootCertificate_length]
    exact f4_conjRange_all
  · fin_cases j
    · exact f4_simpleRow_0
    · exact f4_simpleRow_1
    · exact f4_simpleRow_2
    · exact f4_simpleRow_3

end CFSG.LieType.Chevalley.RootOps
