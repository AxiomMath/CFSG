module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.EvenSmallLie.CatalogOrders

@[expose] def m24LieCheck : Bool :=
  lieSearch [2, 3, 5, 7, 11, 23] 244823040 (fun _ _ _ o => o != 244823040)

end CFSG.EvenSporadicStandard.TwoFi22.DS81
