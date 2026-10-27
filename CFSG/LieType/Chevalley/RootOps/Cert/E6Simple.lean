module

public import Certificates.Certificate51

public import CFSG.LieType.Chevalley.RootOps.CertTools
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e6_simpleRow_0 : simpleRow .E6 ⟨0, by decide⟩ = true := by
  exact Certificates.certificate51.1

theorem e6_simpleRow_1 : simpleRow .E6 ⟨1, by decide⟩ = true := by
  exact Certificates.certificate51.2.1

theorem e6_simpleRow_2 : simpleRow .E6 ⟨2, by decide⟩ = true := by
  exact Certificates.certificate51.2.2.1

theorem e6_simpleRow_3 : simpleRow .E6 ⟨3, by decide⟩ = true := by
  exact Certificates.certificate51.2.2.2.1

theorem e6_simpleRow_4 : simpleRow .E6 ⟨4, by decide⟩ = true := by
  exact Certificates.certificate51.2.2.2.2.1

theorem e6_simpleRow_5 : simpleRow .E6 ⟨5, by decide⟩ = true := by
  exact Certificates.certificate51.2.2.2.2.2

end CFSG.LieType.Chevalley.RootOps
