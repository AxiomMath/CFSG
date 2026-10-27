module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
public import Certificates.Certificate3180
public import Certificates.Certificate3000

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

theorem comm_check :
    commCheck = true :=
  Certificates.certificate3000.1

theorem trans_check :
    transCheck = true :=
  Certificates.certificate3000.2

end CFSG.EvenSmallLie.UnitarySix.Yamada
