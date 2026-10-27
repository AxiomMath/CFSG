module

public import Certificates.Certificate81

public import CFSG.LieType.Steinberg.Adjoint.Cert
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e8Data_checkWeyl_0 : e8Data.checkWeylRange 0 20 = true := by
  exact Certificates.certificate81.1

theorem e8Data_checkWeyl_1 : e8Data.checkWeylRange 20 20 = true := by
  exact Certificates.certificate81.2.1

theorem e8Data_checkWeyl_2 : e8Data.checkWeylRange 40 20 = true := by
  exact Certificates.certificate81.2.2.1

theorem e8Data_checkWeyl_3 : e8Data.checkWeylRange 60 20 = true := by
  exact Certificates.certificate81.2.2.2.1

theorem e8Data_checkWeyl_4 : e8Data.checkWeylRange 80 20 = true := by
  exact Certificates.certificate81.2.2.2.2.1

theorem e8Data_checkWeyl_5 : e8Data.checkWeylRange 100 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.1

theorem e8Data_checkWeyl_6 : e8Data.checkWeylRange 120 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.2.1

theorem e8Data_checkWeyl_7 : e8Data.checkWeylRange 140 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.2.2.1

theorem e8Data_checkWeyl_8 : e8Data.checkWeylRange 160 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.2.2.2.1

theorem e8Data_checkWeyl_9 : e8Data.checkWeylRange 180 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.2.2.2.2.1

theorem e8Data_checkWeyl_10 : e8Data.checkWeylRange 200 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.2.2.2.2.2.1

theorem e8Data_checkWeyl_11 : e8Data.checkWeylRange 220 20 = true := by
  exact Certificates.certificate81.2.2.2.2.2.2.2.2.2.2.2

end CFSG.LieType.Steinberg.Adjoint
