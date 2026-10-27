module

public import CFSG.LocalAnalysis.OddStandard.ThmCDefs

public section

namespace CFSG.OddStandard.ThmC

open Subgroup

theorem mem_of_orderOf_two_of_odd_index {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hidx : ¬ 2 ∣ K.index) {w : X} (hw : orderOf w = 2) : w ∈ K := by
  have h1 : orderOf (QuotientGroup.mk' K w) ∣ 2 := hw ▸ orderOf_map_dvd _ w
  have h2 : orderOf (QuotientGroup.mk' K w) ∣ K.index :=
    orderOf_dvd_natCard (QuotientGroup.mk' K w)
  have h3 : orderOf (QuotientGroup.mk' K w) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 hidx
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff w).1 h3

end CFSG.OddStandard.ThmC
