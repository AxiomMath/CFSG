module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Co2

public section

namespace CFSG.EvenSporadicStandard.Co2Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem center_eq_bot_of_isSporadic {Y : Type} [Group Y]
    (hY : IsSporadic Y .Co2) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.Co2 := e₀
  have hc : Subgroup.center NativeSporadic.Co2 = ⊥ := HypOne.Co2.center_native
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ Subgroup.center NativeSporadic.Co2 := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic Y s) : IsSporadic (Y ⧸ center Y) s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

end CFSG.EvenSporadicStandard.Co2Std

