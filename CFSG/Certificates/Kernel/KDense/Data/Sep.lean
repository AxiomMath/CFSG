module

public import CFSG.Certificates.Kernel.KDense.Data.SepUT0
public import CFSG.Certificates.Kernel.KDense.Data.SepUT1
public import CFSG.Certificates.Kernel.KDense.Data.SepUT2
public import CFSG.Certificates.Kernel.KDense.Data.SepUT3
public import CFSG.Certificates.Kernel.KDense.Data.SepUT4
public import CFSG.Certificates.Kernel.KDense.Data.SepUT5
public import CFSG.Certificates.Kernel.KDense.Data.SepUT6
public import CFSG.Certificates.Kernel.KDense.Data.SepUT7
public import CFSG.Certificates.Kernel.KDense.Data.SepU0
public import CFSG.Certificates.Kernel.KDense.Data.SepU1
public import CFSG.Certificates.Kernel.KDense.Data.SepU2
public import CFSG.Certificates.Kernel.KDense.Data.SepU3
public import CFSG.Certificates.Kernel.KDense.Data.SepMisc

public section

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem ut_ok : utOK CFSG.KD.KDF.OCT UT = true := by kd_andB ut7 ut6 ut5 ut4 ut3 ut2 ut1 ut0

theorem u_ok : uPlanesOK UT U = true := by
  kd_andB u_bound u23 u22 u21 u20 u19 u18 u17 u16 u15 u14 u13 u12 u11 u10 u9 u8 u7 u6 u5 u4 u3 u2 u1 u0

end CFSG.KD.KDS

end
