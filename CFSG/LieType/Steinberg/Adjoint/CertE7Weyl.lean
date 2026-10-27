module

public import Certificates.Certificate79

public import CFSG.LieType.Steinberg.Adjoint.CertE7Data
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e7AdjData_checkWeyl_0 : e7AdjData.checkWeylRange 0 18 = true := by
  exact Certificates.certificate79.1

theorem e7AdjData_checkWeyl_1 : e7AdjData.checkWeylRange 18 18 = true := by
  exact Certificates.certificate79.2.1

theorem e7AdjData_checkWeyl_2 : e7AdjData.checkWeylRange 36 18 = true := by
  exact Certificates.certificate79.2.2.1

theorem e7AdjData_checkWeyl_3 : e7AdjData.checkWeylRange 54 18 = true := by
  exact Certificates.certificate79.2.2.2.1

theorem e7AdjData_checkWeyl_4 : e7AdjData.checkWeylRange 72 18 = true := by
  exact Certificates.certificate79.2.2.2.2.1

theorem e7AdjData_checkWeyl_5 : e7AdjData.checkWeylRange 90 18 = true := by
  exact Certificates.certificate79.2.2.2.2.2.1

theorem e7AdjData_checkWeyl_6 : e7AdjData.checkWeylRange 108 18 = true := by
  exact Certificates.certificate79.2.2.2.2.2.2

end CFSG.LieType.Steinberg.Adjoint
