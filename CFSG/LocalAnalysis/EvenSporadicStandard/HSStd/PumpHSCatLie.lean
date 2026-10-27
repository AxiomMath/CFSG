module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open CFSG.EvenSmallLie.CatalogOrders

@[expose] def hsLieCheck : Bool :=
  lieSearch [2, 3, 5, 7, 11] 44352000 (fun _ _ _ o => o != 44352000)

end CFSG.EvenSporadicStandard.HSStd.PumpHS
