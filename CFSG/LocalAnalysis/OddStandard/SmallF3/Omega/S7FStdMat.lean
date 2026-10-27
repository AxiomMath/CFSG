module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_ctrQ_not_dvd [Finite G] {L : Subgroup G} (hL : InF L) : ¬ ctrQ L ∣ 95040 := by
  obtain ⟨hY, hQ | hQ⟩ := hL
  · rcases hQ with h | h | h | h | h | h
    · rw [ctrQ_of_psp4 hY h]; omega
    · rw [ctrQ_of_l43 hY h]; omega
    · rw [ctrQ_of_u43 hY h]; omega
    · rw [ctrQ_of_omega7 hY h]; omega
    · rw [ctrQ_of_omega8plus hY h]; omega
    · rw [ctrQ_of_omega8minus hY h]; omega
  · rw [ctrQ_of_twoU43 hY hQ]; omega

theorem s7f_card_not_dvd [Finite G] {L : Subgroup G} (hL : InF L) : ¬ Nat.card G ∣ 95040 :=
  fun h => s7f_ctrQ_not_dvd hL
    (((center ↥L).card_quotient_dvd_card).trans ((L.card_subgroup_dvd_card).trans h))

theorem s7f_not_M11 (hM11 : Nat.card NativeSporadic.M11 = 7920) [Finite G] {L : Subgroup G}
    (hL : InF L) : ¬ NativeSporadic.IsSporadic G .M11 := by
  rintro ⟨e⟩
  apply s7f_card_not_dvd hL
  have hG : Nat.card G = 7920 := (Nat.card_congr e.toEquiv).trans hM11
  rw [hG]
  omega

theorem s7f_not_M12 (hM12 : Nat.card NativeSporadic.M12 = 95040) [Finite G] {L : Subgroup G}
    (hL : InF L) : ¬ NativeSporadic.IsSporadic G .M12 := by
  rintro ⟨e⟩
  apply s7f_card_not_dvd hL
  rw [(Nat.card_congr e.toEquiv).trans hM12]

end CFSG.OddStandard.SmallF3.Omega
