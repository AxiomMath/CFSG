module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Dihedral

variable {G : Type*} [Group G]

theorem max_of_card_odd {G : Type} [Group G] [Finite G] {m : ℕ} (hG : Nat.card G = 256 * m)
    (hm : ¬ 2 ∣ m) {S0 R : Subgroup G} (hS0card : Nat.card S0 = 256) (hR : IsPGroup 2 R)
    (hle : S0 ≤ R) : R ≤ S0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
  have h2 : Nat.card R ∣ Nat.card G := Subgroup.card_subgroup_dvd_card R
  rw [hn, hG] at h2
  have hn8 : n ≤ 8 := by
    by_contra h
    have h9 : 2 ^ 9 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have h10 : 2 ^ 9 ∣ 256 * m := h9.trans h2
    apply hm
    have h512 : (2 : ℕ) ^ 9 = 256 * 2 := by norm_num
    have h11 : 256 * 2 ∣ 256 * m := by rw [← h512]; exact h10
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h11
  have hle' : Nat.card R ≤ Nat.card S0 := by
    rw [hn, hS0card]
    calc 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hn8
      _ = 256 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle hle').symm.le

end Dihedral

end CFSG.EvenSporadicStandard.Fin76b
