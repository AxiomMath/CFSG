module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Main

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem ruBalanceHered_of_catalog
    (hC : CatalogNoRu) :
    RuBalanceHered :=
  ruBalanceHered_of_full_aut (catalogNoRuFull_of_catalogNoRu hC) ruAutInner

theorem fi23BalanceHered_of_catalog (hC : CatalogFi23Host) :
    Fi23BalanceHered :=
  fi23BalanceHered_of_full (catalogFi23HostFull_of_catalogFi23Host hC)

end CFSG.EvenSporadicStandard.Induction.Balance
