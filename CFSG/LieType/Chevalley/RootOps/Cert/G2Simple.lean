module

public import Certificates.Certificate74

public import CFSG.LieType.Chevalley.RootOps.CertTools
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem g2_simpleRow_0 : simpleRow .G2 ⟨0, by decide⟩ = true := by
  exact Certificates.certificate74.1

theorem g2_simpleRow_1 : simpleRow .G2 ⟨1, by decide⟩ = true := by
  exact Certificates.certificate74.2

end CFSG.LieType.Chevalley.RootOps
