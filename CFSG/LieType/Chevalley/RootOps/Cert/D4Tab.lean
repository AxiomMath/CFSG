module

public import Certificates.Certificate48

public import CFSG.LieType.Chevalley.RootOps.Instance
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem d4_tabCheck : tabCheck .D4 = true := by
  exact Certificates.certificate48.1

theorem d4_allValid : allValid .D4 = true := by
  exact Certificates.certificate48.2

end CFSG.LieType.Chevalley.RootOps
