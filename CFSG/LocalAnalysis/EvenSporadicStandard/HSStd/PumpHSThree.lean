module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCliqueSpec

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.FiveY

theorem card_centralizer_three_le
    {Y : Type} [Group Y] (hY : IsSporadic Y .HS) {v : Y}
    (hv : orderOf v = 3) : Nat.card ↥(centralizer ({v} : Set Y)) ≤ 720 := by
  obtain ⟨e₀⟩ := hY
  let ε : Y ≃* ↥hs100P := (e₀ : Y ≃* NativeSporadic.HS).trans hs100Equiv
  rw [card_centralizer_mulEquiv_PH ε v]
  set u : ↥hs100P := ε v with hu
  have hu3 : orderOf u = 3 := by rw [hu, MulEquiv.orderOf_eq]; exact hv
  set u' : ↥hs100R := Subgroup.inclusion hs100P_le_R u with hu'
  have hu'3 : orderOf u' = 3 := by
    rw [hu', orderOf_injective _ (Subgroup.inclusion_injective hs100P_le_R)]
    exact hu3
  have h720 := card_centralizer_hs100R_three hu'3
  rw [← h720]
  refine Nat.card_le_card_of_injective
    (fun c => (⟨Subgroup.inclusion hs100P_le_R c.1, ?_⟩ :
      ↥(centralizer ({u'} : Set ↥hs100R)))) ?_
  · rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 c.2
    rw [hu', ← map_mul, ← map_mul, this]
  · intro c d h
    have := Subgroup.inclusion_injective hs100P_le_R (congrArg Subtype.val h)
    exact Subtype.ext this

end CFSG.EvenSporadicStandard.HSStd.PumpHS
