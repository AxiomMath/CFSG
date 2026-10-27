module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Count

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem y7a_normal_eq {G : Type} [Group G] [Finite G] {N X H0 : Subgroup G} {t : G} {S : Set G}
    (hXN : X ≤ N) (hH0X : H0 ≤ X) (hH0 : H0 = N ⊓ centralizer ({t} : Set G))
    (hX : Nat.card ↥X = 32 * Nat.card ↥H0) (hS : ∀ n ∈ N, n * t * n⁻¹ ∈ S)
    (hSc : Nat.card ↥S ≤ 52) : X = N := by
  have hNle : Nat.card ↥N ≤ Nat.card ↥S * Nat.card ↥H0 := y6_orbit_le hH0 hS
  have hNle52 : Nat.card ↥N ≤ 52 * Nat.card ↥H0 :=
    hNle.trans (Nat.mul_le_mul_right _ hSc)
  have hdvd : Nat.card ↥X ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hXN
  obtain ⟨q, hq⟩ := hdvd
  have hH0pos : 0 < Nat.card ↥H0 := Nat.card_pos
  have hqle : q ≤ 1 := by
    rw [hq, hX] at hNle52
    have h : 32 * q * Nat.card ↥H0 ≤ 52 * Nat.card ↥H0 := by nlinarith [hNle52]
    have := Nat.le_of_mul_le_mul_right h hH0pos
    omega
  have hqge : 1 ≤ q := by
    have hXleN : Nat.card ↥X ≤ Nat.card ↥N :=
      Nat.le_of_dvd (Nat.card_pos (α := ↥N)) (Subgroup.card_dvd_of_le hXN)
    have h' : Nat.card ↥X * 1 ≤ Nat.card ↥X * q := by
      rw [hq] at hXleN
      simpa using hXleN
    exact Nat.le_of_mul_le_mul_left h' (Nat.card_pos (α := ↥X))
  have hq1 : q = 1 := le_antisymm hqle hqge
  have hNX : Nat.card ↥N = Nat.card ↥X := by rw [hq, hq1, mul_one]
  exact Subgroup.eq_of_le_of_card_ge hXN (le_of_eq hNX)

end CFSG.OddStandard.HigherRank.YamadaG23
