module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThData
public meta import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThData
public import Certificates.Certificate3005
public meta import Certificates.Data.CFSGNative.SectionRank.Th

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.SectionRank.Native

theorem th_prodOrder_check :
    prodOrderOK (ops2 248) thData.seedA thData.seedB 19 0 = true :=
  Certificates.certificate3005

end CFSG.EvenSmallLie.CatalogOrders
