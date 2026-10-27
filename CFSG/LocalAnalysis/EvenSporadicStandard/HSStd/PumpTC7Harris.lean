module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H39
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H43
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem harrisL39L43NoD8_proved :
    HarrisL39L43NoD8 := by
  intro G _ _ N hN hC hL t ht hD y hy hy3
  have := hN
  have hyC : y ∈ centralizer ({t} : Set G) := by
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact c.2
  rcases hL with h39 | h43
  · exact harrisL39_noD8 N hC h39 ht hD hyC hy3
  · exact harrisL43_noD8 N hC h43 ht hD hyC hy3

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
