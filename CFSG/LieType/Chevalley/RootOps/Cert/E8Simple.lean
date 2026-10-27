module

public import Certificates.Certificate66

public import CFSG.LieType.Chevalley.RootOps.CertTools
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e8_simpleRow_0 : simpleRow .E8 ⟨0, by decide⟩ = true := by
  exact Certificates.certificate66.1

theorem e8_simpleRow_1 : simpleRow .E8 ⟨1, by decide⟩ = true := by
  exact Certificates.certificate66.2.1

theorem e8_simpleRow_2 : simpleRow .E8 ⟨2, by decide⟩ = true := by
  exact Certificates.certificate66.2.2.1

theorem e8_simpleRow_3 : simpleRow .E8 ⟨3, by decide⟩ = true := by
  exact Certificates.certificate66.2.2.2.1

theorem e8_simpleRow_4 : simpleRow .E8 ⟨4, by decide⟩ = true := by
  exact Certificates.certificate66.2.2.2.2.1

theorem e8_simpleRow_5 : simpleRow .E8 ⟨5, by decide⟩ = true := by
  exact Certificates.certificate66.2.2.2.2.2.1

theorem e8_simpleRow_6 : simpleRow .E8 ⟨6, by decide⟩ = true := by
  exact Certificates.certificate66.2.2.2.2.2.2.1

theorem e8_simpleRow_7 : simpleRow .E8 ⟨7, by decide⟩ = true := by
  exact Certificates.certificate66.2.2.2.2.2.2.2

end CFSG.LieType.Chevalley.RootOps
