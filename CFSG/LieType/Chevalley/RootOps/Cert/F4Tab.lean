module

public import Certificates.Certificate71

public import CFSG.LieType.Chevalley.RootOps.Instance
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem f4_tabCheck : tabCheck .F4 = true := by
  exact Certificates.certificate71.1

theorem f4_allValid : allValid .F4 = true := by
  exact Certificates.certificate71.2

end CFSG.LieType.Chevalley.RootOps
