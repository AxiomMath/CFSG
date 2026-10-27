module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup

variable {F : Type} [Group F] [Finite F] (Φ : F →* Z2S6)

theorem dvd_natCard_of_a6Factor_le_range (hA : a6Factor ≤ Φ.range) : 360 ∣ Nat.card F := by
  have h1 : Nat.card a6Factor ∣ Nat.card Φ.range := Subgroup.card_dvd_of_le hA
  rw [card_a6Factor] at h1
  rw [← Subgroup.card_ker_mul_card_range Φ]
  exact dvd_mul_of_dvd_right h1 _

theorem not_two_pow_six_dvd_natCard (hodd : Odd (Nat.card Φ.ker)) : ¬ 2 ^ 6 ∣ Nat.card F := by
  intro h
  rw [← Subgroup.card_ker_mul_card_range Φ] at h
  have hcop : Nat.Coprime (2 ^ 6) (Nat.card Φ.ker) :=
    hodd.coprime_two_left.pow_left 6
  have hrange : 2 ^ 6 ∣ Nat.card Φ.range := hcop.dvd_of_dvd_mul_left h
  have h1440 : 2 ^ 6 ∣ 1440 := by
    rw [← card_z2s6]
    exact hrange.trans (Subgroup.card_subgroup_dvd_card Φ.range)
  norm_num at h1440

theorem orderOf_ne_eight_of_odd_ker (hodd : Odd (Nat.card Φ.ker)) (x : F) : orderOf x ≠ 8 := by
  intro hx
  have hne : orderOf (Φ x) ≠ 8 := z2s6_orderOf_ne_eight (Φ x)
  have h8 : orderOf (Φ x) ∣ 8 := by
    rw [← hx]
    exact orderOf_map_dvd Φ x
  have hdvd4 : orderOf (Φ x) ∣ 4 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at h8
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8
    interval_cases k
    · rw [hk']; norm_num
    · rw [hk']; norm_num
    · rw [hk']; norm_num
    · rw [hk'] at hne; norm_num at hne
  have h4 : (Φ x) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd4
  have hker : x ^ 4 ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, h4]
  have hord : orderOf (x ^ 4) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num : (4 : ℕ) ≠ 0) (by rw [hx]; norm_num), hx]
  have hodd2 : Odd (orderOf (x ^ 4)) :=
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Φ.ker hker)
  rw [hord] at hodd2
  exact Nat.not_odd_iff_even.mpr even_two hodd2

theorem natCard_quotient_ker_dvd : Nat.card (F ⧸ Φ.ker) ∣ 1440 := by
  have h : Nat.card (F ⧸ Φ.ker) = Nat.card Φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
  rw [h]
  calc Nat.card Φ.range ∣ Nat.card Z2S6 := Subgroup.card_subgroup_dvd_card Φ.range
    _ = 1440 := card_z2s6

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
