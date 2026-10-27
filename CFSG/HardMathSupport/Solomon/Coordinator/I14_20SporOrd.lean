module

public import CFSG.HardMathSupport.Foote.E27.SporList
public import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Blueprint CFSG.HardMathSupport.Foote.E27

section Certificates


theorem not_five_mul_dvd_card_carrier (s : TauCeti.SporadicName)
    (hs : s ≠ .Co1 ∧ s ≠ .B ∧ s ≠ .M) :
    ¬ 5 * 64561751654400 ∣ Nat.card (NativeSporadic.Carrier s) := by
  by_cases hbig : s ∈ sporBigNames
  swap
  · intro h
    refine not_three_pow_five_dvd_card_carrier s hbig (dvd_trans ?_ h)
    decide +kernel
  intro h
  simp only [sporBigNames, Finset.mem_insert, Finset.mem_singleton] at hbig
  obtain ⟨h1, h2, h3⟩ := hs
  rcases hbig with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Nat.card (NativeSporadic.Carrier .J3) = _ from CFSG.Sporadic.J3.card_J3] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .McL) = _ from CFSG.Sporadic.McL.card_McL] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Suz) = _ from CFSG.Sporadic.Suz.card_Suz] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Ly) = _ from CFSG.Sporadic.Ly.card_Ly] at h
    exact absurd h (by decide +kernel)
  · exact h1 rfl
  · rw [show Nat.card (NativeSporadic.Carrier .Co2) = _ from CFSG.Sporadic.Co2.card_Co2] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Co3) = _ from CFSG.Sporadic.Co3.card_Co3] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Fi22) = _ from CFSG.Sporadic.Fi22.card_Fi22] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Fi23) = _ from CFSG.Sporadic.Fi23.card_Fi23] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Fi24Prime) = _ from
      CFSG.Sporadic.Fi24.card_Fi24prime] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .HN) = _ from CFSG.Sporadic.HN.card_HN] at h
    exact absurd h (by decide +kernel)
  · rw [show Nat.card (NativeSporadic.Carrier .Th) = _ from CFSG.RankThree.PartOne.CTP.card_Th] at h
    exact absurd h (by decide +kernel)
  · exact h2 rfl
  · exact h3 rfl

end Certificates

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
