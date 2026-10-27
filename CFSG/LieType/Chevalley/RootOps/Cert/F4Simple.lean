module

public import Certificates.Certificate70

public import CFSG.LieType.Chevalley.RootOps.CertTools
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem f4_simpleRow_0 : simpleRow .F4 ⟨0, by decide⟩ = true := by
  exact Certificates.certificate70.1

theorem f4_simpleRow_1 : simpleRow .F4 ⟨1, by decide⟩ = true := by
  exact Certificates.certificate70.2.1

theorem f4_simpleRow_2 : simpleRow .F4 ⟨2, by decide⟩ = true := by
  exact Certificates.certificate70.2.2.1

theorem f4_simpleRow_3 : simpleRow .F4 ⟨3, by decide⟩ = true := by
  exact Certificates.certificate70.2.2.2

end CFSG.LieType.Chevalley.RootOps
