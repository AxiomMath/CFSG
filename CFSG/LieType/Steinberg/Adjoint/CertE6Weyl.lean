module

public import Certificates.Certificate77

public import CFSG.LieType.Steinberg.Adjoint.CertE6
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate118

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e6AdjData_checkWeyl_0 : e6AdjData.checkWeylRange 0 24 = true := by
  exact Certificates.certificate77.1

theorem e6AdjData_checkWeyl_1 : e6AdjData.checkWeylRange 24 24 = true := by
  exact Certificates.certificate77.2.1

theorem e6AdjData_checkWeyl_2 : e6AdjData.checkWeylRange 48 24 = true := by
  exact Certificates.certificate77.2.2

end CFSG.LieType.Steinberg.Adjoint
