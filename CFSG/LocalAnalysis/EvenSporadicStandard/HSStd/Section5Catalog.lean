module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Section5Hered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.StdUHered

public section

namespace CFSG.EvenSporadicStandard.HSStd

open CFSG.ComponentClassification

theorem hsSection5_of_hered (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (h : HSSection5Hered) : HSSection5 :=
  fun G _ _ L hset => h G (hset.1.uHered hCU) L hset

end CFSG.EvenSporadicStandard.HSStd
