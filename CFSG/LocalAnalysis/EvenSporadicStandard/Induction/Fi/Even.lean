module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78LitHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

structure Hyp12Fi : Prop where
  lie : Sol78Hyp12LieHered
  even22 : EvenCoverOutHered [.Fi23, .Fi24Prime] .Fi22

end CFSG.EvenSporadicStandard.Induction.Fi
