module

public import Certificates.Certificate57

public import CFSG.LieType.Chevalley.RootOps.CertTools
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e7_simpleRow_0 : simpleRow .E7 ⟨0, by decide⟩ = true := by
  exact Certificates.certificate57.1

theorem e7_simpleRow_1 : simpleRow .E7 ⟨1, by decide⟩ = true := by
  exact Certificates.certificate57.2.1

theorem e7_simpleRow_2 : simpleRow .E7 ⟨2, by decide⟩ = true := by
  exact Certificates.certificate57.2.2.1

theorem e7_simpleRow_3 : simpleRow .E7 ⟨3, by decide⟩ = true := by
  exact Certificates.certificate57.2.2.2.1

theorem e7_simpleRow_4 : simpleRow .E7 ⟨4, by decide⟩ = true := by
  exact Certificates.certificate57.2.2.2.2.1

theorem e7_simpleRow_5 : simpleRow .E7 ⟨5, by decide⟩ = true := by
  exact Certificates.certificate57.2.2.2.2.2.1

theorem e7_simpleRow_6 : simpleRow .E7 ⟨6, by decide⟩ = true := by
  exact Certificates.certificate57.2.2.2.2.2.2

end CFSG.LieType.Chevalley.RootOps
