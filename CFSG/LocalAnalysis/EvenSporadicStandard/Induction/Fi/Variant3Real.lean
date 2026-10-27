module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutR3

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup
open CFSG.Sporadic.Fi24 (R JR MR)

section Order

theorem fi23Order_real : Fi23Order :=
  CFSG.Sporadic.Fi23.card_Fi23

end Order

section Fixed

theorem fi24OuterFixed_real : Fi24OuterFixed :=
  fun _ _ hY _ hν hnot _ hB hperf hcard =>
    (fi24OutR_class_of_isSporadic hY hν hnot hB hperf hcard).2

end Fixed

end CFSG.EvenSporadicStandard.Induction.Fi.V3
