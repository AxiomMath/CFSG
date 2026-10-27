module

public import Certificates.Certificate67

public import CFSG.LieType.Chevalley.RootOps.Instance
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e8_tabCheck : tabCheck .E8 = true := by
  exact Certificates.certificate67.1

theorem e8_allValid : allValid .E8 = true := by
  exact Certificates.certificate67.2

end CFSG.LieType.Chevalley.RootOps
