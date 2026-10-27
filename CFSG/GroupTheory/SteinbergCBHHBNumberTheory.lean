module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.PrimePowerArith

public section

namespace CFSG.GroupTheory.HallHigmanB

open CFSG.QuasithinUnique.I43Dihedral

theorem odd_pow_sub_one_eq_prime_pow {p n₀ q k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn₀ : 1 ≤ n₀)
    (hq : q.Prime) (hk : 1 ≤ k) (h : p ^ n₀ - 1 = q ^ k) :
    q = 2 ∧ (∃ j, p = Nat.fermatNumber j) ∧ (n₀ = 1 ∨ (p = 3 ∧ n₀ = 2)) := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hp1 : 1 ≤ p ^ n₀ := Nat.one_le_pow _ _ hp.pos
  have hq2 : q = 2 := by
    have heven : Even (p ^ n₀ - 1) := by
      have := (hodd.pow (n := n₀))
      exact Nat.Odd.sub_odd this odd_one
    rw [h] at heven
    have h2 : 2 ∣ q ^ k := even_iff_two_dvd.1 heven
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  subst hq2
  have hpk : p ^ n₀ = 2 ^ k + 1 := by omega
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  ·
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rcases hcases with rfl | rfl | rfl
    ·
      have hn : n₀ = 1 := by
        by_contra hne
        have : p ^ 2 ≤ p ^ n₀ := Nat.pow_le_pow_right hp.pos (by omega)
        nlinarith
      subst hn
      rw [pow_one] at hpk
      exact ⟨⟨0, by rw [hpk]; rfl⟩, Or.inl rfl⟩
    ·
      have hn : n₀ = 1 := by
        by_contra hne
        have : p ^ 2 ≤ p ^ n₀ := Nat.pow_le_pow_right hp.pos (by omega)
        nlinarith
      subst hn
      rw [pow_one] at hpk
      exact ⟨⟨1, by rw [hpk]; rfl⟩, Or.inl rfl⟩
    ·
      have hpk9 : p ^ n₀ = 9 := by rw [hpk]; rfl
      have hp3' : p = 3 := by
        have h3 : p ∣ 9 := ⟨p ^ (n₀ - 1), by rw [← hpk9, ← pow_succ', Nat.sub_add_cancel hn₀]⟩
        have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
        rw [h9] at h3
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
      subst hp3'
      have hn : n₀ = 2 := by
        have : (3 : ℕ) ^ n₀ = 3 ^ 2 := by rw [hpk9]; norm_num
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
      exact ⟨⟨0, rfl⟩, Or.inr ⟨rfl, hn⟩⟩
  · have hn : n₀ = 1 := eq_one_of_primePow_eq_two_pow_add_one hp (by omega) hk4 hpk
    subst hn
    rw [pow_one] at hpk
    have hprime : (2 ^ k + 1).Prime := hpk ▸ hp
    obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) (by omega : k ≠ 0) hprime
    exact ⟨⟨j, by rw [hpk, hj]; rfl⟩, Or.inl rfl⟩

theorem two_pow_sub_one_eq_prime_pow {n₀ q k : ℕ} (hq : q.Prime) (hk : 1 ≤ k)
    (h : 2 ^ n₀ - 1 = q ^ k) : k = 1 ∧ 2 ≤ n₀ ∧ q = mersenne n₀ := by
  have hqk : 2 ≤ q ^ k := le_trans hq.two_le (Nat.le_self_pow (by omega) q)
  have h1 : 1 ≤ 2 ^ n₀ := Nat.one_le_two_pow
  have hn₀ : 2 ≤ n₀ := by
    by_contra hlt
    have : 2 ^ n₀ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk1 : k = 1 := eq_one_of_primePow_add_one_eq_two_pow hq (by omega) hn₀ (by omega)
  subst hk1
  refine ⟨rfl, hn₀, ?_⟩
  rw [mersenne, h, pow_one]

end CFSG.GroupTheory.HallHigmanB
