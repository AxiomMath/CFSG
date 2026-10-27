module

public import Certificates.Certificate52

public import CFSG.LieType.Chevalley.RootOps.Instance
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e6_tabCheck : tabCheck .E6 = true := by
  exact Certificates.certificate52.1

theorem e6_allValid : allValid .E6 = true := by
  exact Certificates.certificate52.2

end CFSG.LieType.Chevalley.RootOps
