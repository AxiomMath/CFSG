module

public import Certificates.Certificate47

public import CFSG.LieType.Chevalley.RootOps.CertTools
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem d4_simpleRow_0 : simpleRow .D4 ⟨0, by decide⟩ = true := by
  exact Certificates.certificate47.1

theorem d4_simpleRow_1 : simpleRow .D4 ⟨1, by decide⟩ = true := by
  exact Certificates.certificate47.2.1

theorem d4_simpleRow_2 : simpleRow .D4 ⟨2, by decide⟩ = true := by
  exact Certificates.certificate47.2.2.1

theorem d4_simpleRow_3 : simpleRow .D4 ⟨3, by decide⟩ = true := by
  exact Certificates.certificate47.2.2.2

end CFSG.LieType.Chevalley.RootOps
