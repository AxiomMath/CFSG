module

public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import Certificates.Data.CFSGNative.CTIB.Coset
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.OddSquareCertInputs
public import Certificates.Certificate3129

public section

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster.B.CTIB.Native

theorem frameCodesOK_eq_true : frameCodesOK = true :=
  Certificates.certificate3129.1

theorem oddWitOK_Y2 :
    oddWitOK 1 6 wordY2a 8 3 wordY2b 4 3 37440 4112 = true :=
  Certificates.certificate3129.2.1

theorem oddWitOK_CY2 :
    oddWitOK 1 7 wordCY2a 4 3 wordCY2b 4 3 2096 4112 = true :=
  Certificates.certificate3129.2.2.1

theorem oddWitOK_Y3 :
    oddWitOK 32 7 wordY3a 1 3 wordY3b 2 3 102610 16 = true :=
  Certificates.certificate3129.2.2.2

end CFSG.EvenSmallLie.TwoE6
