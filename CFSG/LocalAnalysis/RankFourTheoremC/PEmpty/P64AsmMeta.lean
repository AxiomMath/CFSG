module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open Finset Subgroup

section Conj

variable {G : Type*} [Group G]

theorem conj_pow_eq {x y : G} {ρ : ℕ} (h : y * x * y⁻¹ = x ^ ρ) (k : ℕ) :
    y ^ k * x * (y ^ k)⁻¹ = x ^ (ρ ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := by
      group
    rw [h1, ih, ← conj_pow, h, ← pow_mul, pow_succ']

theorem mul_pow_eq {x y : G} {ρ : ℕ} (h : y * x * y⁻¹ = x ^ ρ) (n : ℕ) :
    (x * y) ^ n = x ^ (∑ k ∈ range n, ρ ^ k) * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y ^ n * x = x ^ (ρ ^ n) * y ^ n := by
      have h2 := conj_pow_eq h n
      calc y ^ n * x = (y ^ n * x * (y ^ n)⁻¹) * y ^ n := by group
        _ = x ^ (ρ ^ n) * y ^ n := by rw [h2]
    rw [pow_succ, ih, Finset.sum_range_succ, pow_add, pow_succ]
    calc x ^ (∑ k ∈ range n, ρ ^ k) * y ^ n * (x * y)
        = x ^ (∑ k ∈ range n, ρ ^ k) * (y ^ n * x) * y := by simp only [mul_assoc]
      _ = x ^ (∑ k ∈ range n, ρ ^ k) * x ^ (ρ ^ n) * (y ^ n * y) := by
        rw [h1]
        simp only [mul_assoc]

end Conj

theorem geom_sum_modEq {p ρ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hρ : ρ ≡ 1 [MOD p]) :
    (∑ k ∈ range p, ρ ^ k) ≡ p [MOD p ^ 2] := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hρ1 : 1 ≤ ρ := by
    by_contra h
    have h0 : ρ = 0 := by omega
    rw [h0] at hρ
    have : (0 : ℕ) = 1 % p := hρ
    rw [Nat.mod_eq_of_lt hp.one_lt] at this
    omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hρ1).mp hρ.symm
  have hρt : ρ = 1 + p * t := by omega
  subst hρt
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have hpp : (p : ZMod (p ^ 2)) * p = 0 := by
    rw [← Nat.cast_mul, ← sq]
    exact ZMod.natCast_self _
  have haa : ((p : ZMod (p ^ 2)) * t) * ((p : ZMod (p ^ 2)) * t) = 0 := by
    calc ((p : ZMod (p ^ 2)) * t) * ((p : ZMod (p ^ 2)) * t)
        = ((p : ZMod (p ^ 2)) * p) * (t * t) := by ring
      _ = 0 := by rw [hpp, zero_mul]
  have hpowa : ∀ k : ℕ, (1 + (p : ZMod (p ^ 2)) * t) ^ k = 1 + k * ((p : ZMod (p ^ 2)) * t) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (1 + (p : ZMod (p ^ 2)) * t) ^ (k + 1) =
          (1 + (p : ZMod (p ^ 2)) * t) ^ k * (1 + (p : ZMod (p ^ 2)) * t) := pow_succ _ _
      rw [h1, ih]
      calc (1 + (k : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * t)) * (1 + (p : ZMod (p ^ 2)) * t)
          = 1 + ((k + 1 : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * t) +
              k * (((p : ZMod (p ^ 2)) * t) * ((p : ZMod (p ^ 2)) * t)) := by
            push_cast
            ring
        _ = 1 + ((k + 1 : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * t) := by
            rw [haa]
            simp
  simp_rw [hpowa]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Nat.cast_sum, Finset.sum_range_id]
  obtain ⟨q, hq⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hsum : p * (p - 1) / 2 = p * q := by
    have h2 : p - 1 = 2 * q := by omega
    rw [h2, show p * (2 * q) = 2 * (p * q) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : ((p * q : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * t) = 0 := by
    calc ((p * q : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * t)
        = ((p : ZMod (p ^ 2)) * p) * (q * t) := by push_cast; ring
      _ = 0 := by rw [hpp, zero_mul]
  rw [this, add_zero]

theorem comm_of_pow_eq_one {G : Type*} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {d g : G} (hd : d ^ p = 1) (hg : orderOf g = p ^ m)
    (hdg : d * g * d⁻¹ ∈ zpowers g) {s i : ℕ} (hy : (g ^ s * d ^ i) ^ p = 1) :
    d * g ^ s = g ^ s * d := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hg1 : g = 1 := by simpa using hg
    subst hg1
    simp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, d * g * d⁻¹ = g ^ r := by
    obtain ⟨r, hr⟩ := (mem_powers_iff_mem_zpowers).mpr hdg
    exact ⟨r, hr.symm⟩
  have hr1 : r ≡ 1 [MOD p] := by
    have h1 := conj_pow_eq hr p
    rw [hd] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    have h2 : g ^ (r ^ p) = g ^ 1 := by rw [pow_one]; exact h1.symm
    have h3 : r ^ p ≡ 1 [MOD p ^ m] := by
      have := (pow_eq_pow_iff_modEq).mp h2
      rwa [hg] at this
    have h4 : r ^ p ≡ 1 [MOD p] :=
      Nat.ModEq.of_dvd (dvd_pow_self p hm.ne') h3
    rw [← ZMod.natCast_eq_natCast_iff] at h4 ⊢
    push_cast at h4 ⊢
    rwa [ZMod.pow_card] at h4
  have hdx : d * g ^ s * d⁻¹ = (g ^ s) ^ r := by
    rw [← conj_pow, hr, ← pow_mul, ← pow_mul, mul_comm]
  have hdi : d ^ i * g ^ s * (d ^ i)⁻¹ = (g ^ s) ^ (r ^ i) := conj_pow_eq hdx i
  have hS := mul_pow_eq hdi p
  have hdip : (d ^ i) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hd, one_pow]
  rw [hdip, mul_one] at hS
  have hS1 : g ^ (s * ∑ k ∈ range p, (r ^ i) ^ k) = 1 := by
    rw [pow_mul, ← hS]
    exact hy
  have hdvd : p ^ m ∣ s * ∑ k ∈ range p, (r ^ i) ^ k := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hS1
  have hmod := geom_sum_modEq hp hp2 (by simpa using hr1.pow i)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hu : ∃ u, (∑ k ∈ range p, (r ^ i) ^ k) = p * u ∧ Nat.Coprime p u := by
    refine ⟨p * ((∑ k ∈ range p, (r ^ i) ^ k) / p ^ 2) + 1, ?_, ?_⟩
    · generalize (∑ k ∈ range p, (r ^ i) ^ k) = S at hmod ⊢
      have h1 := Nat.div_add_mod S (p ^ 2)
      have h2 : S % p ^ 2 = p := by
        rw [hmod]
        exact Nat.mod_eq_of_lt (by nlinarith [hp.two_le])
      rw [h2] at h1
      calc S = p ^ 2 * (S / p ^ 2) + p := h1.symm
        _ = p * (p * (S / p ^ 2) + 1) := by ring
    · simp
  obtain ⟨u, hSu, hcop⟩ := hu
  rw [hSu, ← mul_assoc, mul_comm s p, mul_assoc, pow_succ'] at hdvd
  have hdvd2 : p ^ m' ∣ s * u := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
  have hps : p ^ m' ∣ s := (Nat.Coprime.pow_left m' hcop).dvd_of_dvd_mul_right hdvd2
  have hr1' : p ∣ r - 1 := by
    have hrpos : 1 ≤ r := by
      by_contra h
      have h0 : r = 0 := by omega
      rw [h0] at hr1
      have : (0 : ℕ) = 1 % p := hr1
      rw [Nat.mod_eq_of_lt hp.one_lt] at this
      omega
    exact (Nat.modEq_iff_dvd' hrpos).mp hr1.symm
  have hrpos : 1 ≤ r := by
    by_contra h
    have h0 : r = 0 := by omega
    rw [h0] at hr1
    have : (0 : ℕ) = 1 % p := hr1
    rw [Nat.mod_eq_of_lt hp.one_lt] at this
    omega
  have hone : g ^ (s * (r - 1)) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hg]
    obtain ⟨v, hv⟩ := hr1'
    obtain ⟨s', hs'⟩ := hps
    exact ⟨s' * v, by rw [hs', hv]; ring⟩
  have hsr : s * r = s + s * (r - 1) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hcomm : d * g ^ s * d⁻¹ = g ^ s := by
    rw [hdx, ← pow_mul, hsr, pow_add, hone, mul_one]
  exact mul_inv_eq_iff_eq_mul.mp hcomm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
