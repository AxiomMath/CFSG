module

public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionData
public meta import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionData
public import Certificates.Certificate6000
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23Base
public meta import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.OddStandard

open CFSG.Sporadic.Schreier

theorem m11_rows1_check :
    oddRowsCheck 11 m11CentQ1 m11Cg1 m11Primes1 m11Specs1 2000 = true :=
  Certificates.certificate6000.1

theorem m12_rows1_check :
    oddRowsCheck 12 m12CentQ1 m12Cg1 m12Primes1 m12Specs1 2000 = true :=
  Certificates.certificate6000.2.1

theorem m12_rows2_check :
    oddRowsCheck 12 m12CentQ2 m12Cg2 m12Primes2 m12Specs2 2000 = true :=
  Certificates.certificate6000.2.2.1

theorem m22_rows1_check :
    oddRowsCheck 22 m22CentQ1 m22Cg1 m22Primes1 m22Specs1 2000 = true :=
  Certificates.certificate6000.2.2.2.1

theorem m23_rows1_check :
    oddRowsCheck 23 m23CentQ1 m23Cg1 m23Primes1 m23Specs1 2000 = true :=
  Certificates.certificate6000.2.2.2.2.1

theorem m24_rows1_check :
    oddRowsCheck 24 m24CentQ1 m24Cg1 m24Primes1 m24Specs1 2000 = true :=
  Certificates.certificate6000.2.2.2.2.2.1

theorem m24_rows2_check :
    oddRowsCheck 24 m24CentQ2 m24Cg2 m24Primes2 m24Specs2 2000 = true :=
  Certificates.certificate6000.2.2.2.2.2.2

end CFSG.OddStandard
