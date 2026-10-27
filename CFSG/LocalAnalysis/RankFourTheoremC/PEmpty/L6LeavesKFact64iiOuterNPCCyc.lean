module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCArith
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

theorem pow_zpow_mul_eq {G : Type*} [Group G] {g₀ f : G} {m : ℤ}
    (hm : f * g₀ * f⁻¹ = g₀ ^ m) (s : ℤ) (k : ℕ) :
    (g₀ ^ s * f) ^ k = g₀ ^ (s * ∑ i ∈ Finset.range k, m ^ i) * f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : f ^ k * g₀ ^ s = g₀ ^ (s * m ^ k) * f ^ k := by
      have := pow_conj_zpow hm k s
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    rw [pow_succ, ih, Finset.sum_range_succ, mul_add, zpow_add]
    calc g₀ ^ (s * ∑ i ∈ Finset.range k, m ^ i) * f ^ k * (g₀ ^ s * f)
        = g₀ ^ (s * ∑ i ∈ Finset.range k, m ^ i) * (f ^ k * g₀ ^ s) * f := by group
      _ = g₀ ^ (s * ∑ i ∈ Finset.range k, m ^ i) * (g₀ ^ (s * m ^ k) * f ^ k) * f := by rw [h1]
      _ = g₀ ^ (s * ∑ i ∈ Finset.range k, m ^ i) * g₀ ^ (s * m ^ k) * f ^ (k + 1) := by
        rw [pow_succ]; group

theorem exists_conj_eq_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {g₀ f : G} {a : ℕ} (ha : orderOf g₀ = p ^ a) (hf : f ^ p = 1) {m : ℤ}
    (hm : f * g₀ * f⁻¹ = g₀ ^ m) (hne : f * g₀ * f⁻¹ ≠ g₀) {t : G}
    (ht : t ∈ Subgroup.zpowers g₀) (htf : (t * f) ^ p = 1) :
    ∃ z ∈ Subgroup.zpowers g₀, z * f * z⁻¹ = t * f := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    have : g₀ = 1 := by rwa [pow_zero, orderOf_eq_one_iff] at ha
    subst this
    exact absurd (by simp) hne
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpa : ((p ^ a : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) ^ (a - 1) := by
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  have h1 : ((p ^ a : ℕ) : ℤ) ∣ m ^ p - 1 := by
    have h := pow_conj_zpow hm p 1
    rw [hf, one_mul, zpow_one, inv_one, mul_one, one_mul] at h
    have h2 : g₀ ^ (m ^ p - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← h, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.2 h2
    rwa [ha] at this
  have h2 : (p : ℤ) ∣ m - 1 := by
    have h3 : ((p : ℕ) : ℤ) ∣ m ^ p - 1 :=
      (Dvd.intro ((p : ℤ) ^ (a - 1)) hpa.symm).trans h1
    have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd (m ^ p - 1) p).2 h3
    push_cast at h4
    rw [ZMod.pow_card] at h4
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m - 1) p).1 ?_
    push_cast
    exact h4
  obtain ⟨n₁, hn₁, hsum⟩ := exists_sum_pow_eq_mul hp2 h2
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h5 : ((p ^ a : ℕ) : ℤ) ∣ s * ((p : ℤ) * n₁) := by
    have h6 := pow_zpow_mul_eq hm s p
    rw [hsum, hf, mul_one, htf] at h6
    have := orderOf_dvd_iff_zpow_eq_one.2 h6.symm
    rwa [ha] at this
  have h7 : (p : ℤ) ^ (a - 1) ∣ s := by
    have h8 : (p : ℤ) * (p : ℤ) ^ (a - 1) ∣ (p : ℤ) * (s * n₁) := by
      rw [hpa] at h5
      have : s * ((p : ℤ) * n₁) = (p : ℤ) * (s * n₁) := by ring
      rwa [this] at h5
    have h9 : (p : ℤ) ^ (a - 1) ∣ s * n₁ := (mul_dvd_mul_iff_left hp0).1 h8
    have h10 : IsCoprime ((p : ℤ) ^ (a - 1)) n₁ :=
      IsCoprime.pow_left ((Nat.prime_iff_prime_int.1 hp.out).coprime_iff_not_dvd.2 hn₁)
    exact h10.dvd_of_dvd_mul_right h9
  have hγa : (Int.gcd (m - 1) ((p ^ a : ℕ) : ℤ)) ∣ p ^ a := by
    have := Int.gcd_dvd_right (a := m - 1) (b := ((p ^ a : ℕ) : ℤ))
    exact_mod_cast this
  obtain ⟨e, he, hγe⟩ := (Nat.dvd_prime_pow hp.out).1 hγa
  have hea : e ≠ a := by
    rintro rfl
    have h1' : ((Int.gcd (m - 1) ((p ^ e : ℕ) : ℤ) : ℕ) : ℤ) ∣ m - 1 :=
      Int.gcd_dvd_left (a := m - 1) (b := ((p ^ e : ℕ) : ℤ))
    rw [hγe] at h1'
    have h2' : g₀ ^ (m - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [ha]; exact h1')
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h2'
    exact hne (hm.trans h2')
  have hγs : ((Int.gcd (m - 1) ((p ^ a : ℕ) : ℤ) : ℕ) : ℤ) ∣ s := by
    have h1' : Int.gcd (m - 1) ((p ^ a : ℕ) : ℤ) ∣ p ^ (a - 1) := by
      rw [hγe]
      exact pow_dvd_pow p (by omega)
    have h2' : ((Int.gcd (m - 1) ((p ^ a : ℕ) : ℤ) : ℕ) : ℤ) ∣ (p : ℤ) ^ (a - 1) := by
      exact_mod_cast h1'
    exact h2'.trans h7
  obtain ⟨s', hs'⟩ := hγs
  have hbez := Int.gcd_eq_gcd_ab (m - 1) ((p ^ a : ℕ) : ℤ)
  set x := Int.gcdA (m - 1) ((p ^ a : ℕ) : ℤ) with hx
  set y := Int.gcdB (m - 1) ((p ^ a : ℕ) : ℤ) with hy
  refine ⟨g₀ ^ (-s' * x), Subgroup.zpow_mem _ (Subgroup.mem_zpowers g₀) _, ?_⟩
  have hz : g₀ ^ (-s' * x) * f * (g₀ ^ (-s' * x))⁻¹ = g₀ ^ ((-s' * x) * (1 - m)) * f := by
    have h3 : f ^ 1 * g₀ ^ (-(-s' * x)) * (f ^ 1)⁻¹ = g₀ ^ (-(-s' * x) * m ^ 1) :=
      pow_conj_zpow hm 1 _
    rw [pow_one] at h3
    calc g₀ ^ (-s' * x) * f * (g₀ ^ (-s' * x))⁻¹
        = g₀ ^ (-s' * x) * (f * g₀ ^ (-(-s' * x)) * f⁻¹) * f := by
          rw [← zpow_neg g₀ (-s' * x)]
          group
      _ = g₀ ^ ((-s' * x) * (1 - m)) * f := by
          rw [h3, ← zpow_add]
          congr 2
          ring
  rw [hz]
  congr 1
  have h8 : g₀ ^ ((-s' * x) * (1 - m) - s) = 1 := by
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [ha]
    refine ⟨-s' * y, ?_⟩
    rw [hs']
    linear_combination (-s') * hbez
  rw [zpow_sub, mul_inv_eq_one] at h8
  exact h8

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC
