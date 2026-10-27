module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistConcrete

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup CFSG.LocalAnalysis.SymplecticFourStandard
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis

theorem bothTrivialOddFieldNoSwap_holds : BothTrivialCases.BothTrivialOddFieldNoSwap := by
  intro G _ _ L K _ _ _ n φ t
  unfold BothTrivialCases.OddFieldNoSwap
  intro _ _ _ _ h hbt _ hfield u huC huT hU huu
  obtain ⟨α, hex, hF⟩ := hfield Axis.one
  exact BothTrivialTwistConcrete.false_of_swap h hbt hex hF huC huT hU huu

end CFSG.LocalAnalysis.EvenBN.Sp4
