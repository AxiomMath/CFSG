module

public import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowSubOneExponentDvd

open Finset

private theorem lt_geom_sum {x s : ℕ} (hx : 2 ≤ x) (hs : 2 ≤ s) : s < ∑ i ∈ range s, x ^ i := by
  calc s = ∑ _i ∈ range s, 1 := by simp
    _ < ∑ i ∈ range s, x ^ i := by
      refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ (by omega)) ⟨1, ?_, ?_⟩
      · exact Finset.mem_range.2 (by omega)
      · simpa using (by omega : 1 < x)

private theorem dvd_of_dvd_geom_sum {x s r : ℕ} (hx : 1 ≤ x) (hrx : r ∣ x - 1)
    (hrΦ : r ∣ ∑ i ∈ range s, x ^ i) : r ∣ s := by
  have hsplit : ∑ i ∈ range s, (x ^ i - 1) + s = ∑ i ∈ range s, x ^ i := by
    have h1 : ∑ i ∈ range s, ((x ^ i - 1) + 1) = ∑ i ∈ range s, x ^ i :=
      Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
    rw [← h1, Finset.sum_add_distrib]
    simp
  have hdvd : r ∣ ∑ i ∈ range s, (x ^ i - 1) :=
    Finset.dvd_sum fun i _ => hrx.trans (Nat.sub_one_dvd_pow_sub_one x i)
  rw [← hsplit] at hrΦ
  exact (Nat.dvd_add_right hdvd).1 hrΦ

theorem exists_prime_dvd_pow_sub_one_not_dvd {x s : ℕ} (hx : 2 ≤ x) (hxe : Even x) (hs : s.Prime) :
    ∃ r : ℕ, r.Prime ∧ r ∣ x ^ s - 1 ∧ ¬ r ∣ x - 1 := by
  by_contra hcon
  push Not at hcon
  set Φ := ∑ i ∈ range s, x ^ i
  have hΦmul : Φ * (x - 1) = x ^ s - 1 := geom_sum_mul_of_one_le (by omega) s
  have hΦdvd : Φ ∣ x ^ s - 1 := Dvd.intro _ hΦmul
  have hsΦ : s < Φ := lt_geom_sum hx hs.two_le
  have hΦ0 : Φ ≠ 0 := by omega
  have hprime : ∀ {r : ℕ}, r.Prime → r ∣ Φ → r = s := fun {r} hr hrΦ =>
    (Nat.prime_dvd_prime_iff_eq hr hs).1 (dvd_of_dvd_geom_sum (by omega) (hcon r hr (hrΦ.trans hΦdvd)) hrΦ)
  have hsΦdvd : s ∣ Φ := by
    obtain ⟨r, hr, hrΦ⟩ := Nat.exists_prime_and_dvd (show Φ ≠ 1 by have := hs.two_le; omega)
    rwa [hprime hr hrΦ] at hrΦ
  have hsx : s ∣ x - 1 := hcon s hs (hsΦdvd.trans hΦdvd)
  have hsnx : ¬ s ∣ x := by
    intro h
    have h1 : s ∣ (x - 1) + 1 := by rwa [Nat.sub_add_cancel (by omega)]
    exact hs.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hsx).1 h1))
  have hsodd : Odd s := hs.odd_of_ne_two fun h2 => hsnx (h2 ▸ even_iff_two_dvd.1 hxe)
  haveI : Fact s.Prime := ⟨hs⟩
  have hlte : padicValNat s (x ^ s - 1 ^ s) = padicValNat s (x - 1) + padicValNat s s :=
    padicValNat.pow_sub_pow hsodd (by omega) hsx hsnx hs.ne_zero
  rw [one_pow, padicValNat_self, ← hΦmul, padicValNat.mul hΦ0 (by omega)] at hlte
  have hv : padicValNat s Φ = 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Φ = s ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hΦ0 hprime⟩
  rw [hk, padicValNat.prime_pow] at hv
  rw [hk, hv, pow_one] at hsΦ
  exact lt_irrefl _ hsΦ

theorem dvd_of_forall_prime_dvd {e N : ℕ} (he : 0 < e)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ e - 1 → r ∣ 2 ^ N - 1) : e ∣ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact dvd_zero e
  have hpg : ∀ r : ℕ, r.Prime → r ∣ 2 ^ e - 1 → r ∣ 2 ^ Nat.gcd e N - 1 := by
    intro r hr hre
    have h1 := Nat.dvd_gcd hre (h r hr hre)
    rwa [Nat.pow_sub_one_gcd_pow_sub_one] at h1
  have hg0 : 0 < Nat.gcd e N := Nat.gcd_pos_of_pos_left N he
  have hgN : Nat.gcd e N ∣ N := Nat.gcd_dvd_right e N
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left e N
  generalize Nat.gcd e N = g at hpg hg0 hgN hm
  by_cases hm1 : m = 1
  · rw [hm, hm1, mul_one]
    exact hgN
  exfalso
  have hs : m.minFac.Prime := Nat.minFac_prime hm1
  obtain ⟨r, hr, hrx, hnot⟩ := exists_prime_dvd_pow_sub_one_not_dvd (Nat.le_self_pow hg0.ne' 2)
    ((Nat.even_pow' hg0.ne').2 even_two) hs
  refine hnot (hpg r hr (hrx.trans ?_))
  rw [← pow_mul, hm]
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.mul_dvd_mul_left g (Nat.minFac_dvd m))

theorem exists_prime_dvd_ne {e : ℕ} (he : 2 ≤ e) (h : ¬ IsPrimePow (2 ^ e - 1)) (r : ℕ) :
    ∃ r' : ℕ, r'.Prime ∧ r' ∣ 2 ^ e - 1 ∧ r' ≠ r := by
  have h3 : 2 ≤ 2 ^ e - 1 := by
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  obtain ⟨r', hr', hne⟩ := ((Nat.not_isPrimePow_iff_nontrivial_of_two_le h3).1 h).exists_ne r
  obtain ⟨hp, hd, -⟩ := Nat.mem_primeFactors.1 hr'
  exact ⟨r', hp, hd, hne⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowSubOneExponentDvd
