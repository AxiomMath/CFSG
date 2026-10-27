module

public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace GL83.I243.Gen

open Finset

theorem exists_one_add_pow_eq (d : ℤ) (n : ℕ) :
    ∃ q : ℤ, (1 + d) ^ n = 1 + n * d + d ^ 2 * q := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨q + n + d * q, by rw [pow_succ, hq]; push_cast; ring⟩

theorem exists_sum_one_add_pow_eq (d : ℤ) (n : ℕ) :
    ∃ q : ℤ, ∑ i ∈ range n, (1 + d) ^ i = n + d * (n.choose 2 : ℕ) + d ^ 2 * q := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨r, hr⟩ := exists_one_add_pow_eq d n
    refine ⟨q + r, ?_⟩
    have hc : ((n + 1).choose 2 : ℕ) = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [sum_range_succ, hq, hr, hc]
    push_cast
    ring

theorem sq_dvd_sum_one_add_pow_sub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℤ}
    (hd : (p : ℤ) ∣ d) : (p : ℤ) ^ 2 ∣ ∑ i ∈ range p, (1 + d) ^ i - p := by
  obtain ⟨q, hq⟩ := exists_sum_one_add_pow_eq d p
  have hc : (p : ℤ) ∣ (p.choose 2 : ℕ) :=
    Int.natCast_dvd_natCast.2
      (hp.dvd_choose_self (by norm_num) (lt_of_le_of_ne hp.two_le (Ne.symm hp2)))
  have h1 : (p : ℤ) ^ 2 ∣ d * (p.choose 2 : ℕ) := by
    rw [sq]
    exact mul_dvd_mul hd hc
  have h2 : (p : ℤ) ^ 2 ∣ d ^ 2 * q := (pow_dvd_pow_of_dvd hd 2).mul_right q
  have h3 : ∑ i ∈ range p, (1 + d) ^ i - p = d * (p.choose 2 : ℕ) + d ^ 2 * q := by
    rw [hq]
    ring
  rw [h3]
  exact h1.add h2

theorem sum_pow_modEq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : ℕ} (hu : u ≡ 1 [MOD p]) :
    ∑ i ∈ range p, u ^ i ≡ p [MOD p ^ 2] := by
  have hd : (p : ℤ) ∣ (u : ℤ) - 1 := Nat.modEq_iff_dvd.1 hu.symm
  have h := sq_dvd_sum_one_add_pow_sub hp hp2 hd
  simp only [add_sub_cancel] at h
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact (dvd_sub_comm).1 h

theorem modEq_one_of_pow_modEq_one {p : ℕ} (hp : p.Prime) {u : ℕ} (h : u ^ p ≡ 1 [MOD p]) :
    u ≡ 1 [MOD p] := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  push_cast at h ⊢
  rwa [ZMod.pow_card] at h

section Group

variable {Z : Type*} [CommGroup Z]

theorem exists_map_div_eq_inv_pow (t : Monoid.End Z) (n : ℕ) (ζ : Z)
    (hN : ∏ i ∈ range n, (t ^ i) ζ = 1) : ∃ c : Z, t c / c = (ζ ^ n)⁻¹ := by
  refine ⟨∏ i ∈ range n, ∏ j ∈ range i, (t ^ j) ζ, ?_⟩
  have key : ∀ i : ℕ, t (∏ j ∈ range i, (t ^ j) ζ) / ∏ j ∈ range i, (t ^ j) ζ
      = (t ^ i) ζ / ζ := by
    intro i
    have h1 : t (∏ j ∈ range i, (t ^ j) ζ) = ∏ j ∈ range i, (t ^ (j + 1)) ζ := by
      rw [map_prod]
      refine prod_congr rfl fun j _ => ?_
      rw [pow_succ']
      rfl
    have h2 : ∏ j ∈ range i, ((t ^ (j + 1)) ζ / (t ^ j) ζ) = (t ^ i) ζ / ζ := by
      simpa using prod_range_div (fun j => (t ^ j) ζ) i
    rw [h1, ← prod_div_distrib, h2]
  rw [map_prod, ← prod_div_distrib]
  simp_rw [key]
  rw [prod_div_distrib, hN, prod_const, card_range, one_div]

variable [Finite Z] {p : ℕ} {t : Monoid.End Z} {z : Z}

theorem pow_eq_one_of_sq_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ^ p = 1)
    (hzp : orderOf z = p) (hΩ : ∀ c : Z, c ^ p = 1 → c ∈ Subgroup.zpowers z) {y : Z}
    (hy : y ^ p ^ 2 = 1) (hN : ∏ i ∈ range p, (t ^ i) y = 1) : y ^ p = 1 := by
  by_contra hne
  haveI := Fact.mk hp
  have hord : orderOf y = p ^ 2 := orderOf_eq_prime_pow (n := 1) (by simpa using hne) hy
  have hyp : y ^ p ∈ Subgroup.zpowers z := hΩ _ (by rw [← pow_mul, ← sq]; exact hy)
  have hordp : orderOf (y ^ p) = p :=
    orderOf_eq_prime (by rw [← pow_mul, ← sq]; exact hy) hne
  have hW : Subgroup.zpowers (y ^ p) = Subgroup.zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyp) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hzp, hordp]
  have hzy : Subgroup.zpowers z ≤ Subgroup.zpowers y := by
    rw [← hW]
    exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) p)
  have key : ∀ b : Z, b ^ p ^ 2 = 1 → b ∈ Subgroup.zpowers y := by
    intro b hb
    have hbp : b ^ p ∈ Subgroup.zpowers (y ^ p) := by
      rw [hW]
      exact hΩ _ (by rw [← pow_mul, ← sq]; exact hb)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hbp
    have hmy : (y ^ m) ^ p = (y ^ p) ^ m := by
      rw [← zpow_natCast, ← zpow_natCast y p, ← zpow_mul, ← zpow_mul, mul_comm]
    have h1 : b * (y ^ m)⁻¹ ∈ Subgroup.zpowers z := by
      apply hΩ
      rw [mul_pow, inv_pow, hmy, hm, mul_inv_cancel]
    have h2 := Subgroup.mul_mem _ (hzy h1) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) m)
    simpa using h2
  have hty : t y ∈ Subgroup.zpowers y := key _ (by rw [← map_pow, hy, map_one])
  obtain ⟨u, hu⟩ : ∃ u : ℕ, y ^ u = t y :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hty)
  have hti : ∀ i : ℕ, (t ^ i) y = y ^ (u ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ']
      show t ((t ^ i) y) = _
      rw [ih, map_pow, ← hu, ← pow_mul, pow_succ, mul_comm]
  have h1 : y ^ (u ^ p) = y ^ 1 := by
    rw [← hti, ht, pow_one]
    rfl
  have h2 : u ^ p ≡ 1 [MOD p ^ 2] := by
    have := pow_eq_pow_iff_modEq.1 h1
    rwa [hord] at this
  have h3 : u ≡ 1 [MOD p] :=
    modEq_one_of_pow_modEq_one hp (h2.of_dvd (dvd_pow_self p two_ne_zero))
  have h4 := sum_pow_modEq hp hp2 h3
  have h5 : y ^ (∑ i ∈ range p, u ^ i) = y ^ p := by
    rw [pow_eq_pow_iff_modEq, hord]
    exact h4
  have h6 : ∏ i ∈ range p, (t ^ i) y = y ^ (∑ i ∈ range p, u ^ i) := by
    rw [← prod_pow_eq_pow_sum]
    exact prod_congr rfl fun i _ => hti i
  exact hne (by rw [← h5, ← h6, hN])

theorem pow_eq_one_of_prod_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ^ p = 1)
    (hzp : orderOf z = p) (hΩ : ∀ c : Z, c ^ p = 1 → c ∈ Subgroup.zpowers z) {x : Z} {j : ℕ}
    (hx : x ^ p ^ j = 1) (hN : ∏ i ∈ range p, (t ^ i) x = 1) : x ^ p = 1 := by
  induction j using Nat.strong_induction_on generalizing x with
  | _ j ih =>
    rcases j with _ | _ | j
    · have : x = 1 := by simpa using hx
      rw [this, one_pow]
    · simpa using hx
    · set y := x ^ p ^ j with hy
      have hy2 : y ^ p ^ 2 = 1 := by
        rw [hy, ← pow_mul, ← pow_add]
        exact hx
      have hyN : ∏ i ∈ range p, (t ^ i) y = 1 := by
        simp only [hy, map_pow, prod_pow, hN, one_pow]
      have hyp : y ^ p = 1 := pow_eq_one_of_sq_pow_eq_one hp hp2 ht hzp hΩ hy2 hyN
      refine ih (j + 1) (by omega) ?_ hN
      rw [pow_succ, pow_mul]
      exact hyp

theorem exists_mul_inv_map_mem_zpowers (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ^ p = 1)
    (hzp : orderOf z = p) (hΩ : ∀ c : Z, c ^ p = 1 → c ∈ Subgroup.zpowers z) {ζ : Z}
    (hN : ∏ i ∈ range p, (t ^ i) ζ = 1) : ∃ c : Z, ζ * (c⁻¹ * t c) ∈ Subgroup.zpowers z := by
  obtain ⟨c₀, hc₀⟩ := exists_map_div_eq_inv_pow t p ζ hN
  obtain ⟨e, m', hm', hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos ζ).ne' p hp.ne_one
  obtain ⟨r, s, hrs⟩ : IsCoprime (p : ℤ) (m' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm')
  refine ⟨c₀ ^ r, ?_⟩
  have h1 : (c₀ ^ r)⁻¹ * t (c₀ ^ r) = ((ζ ^ p)⁻¹) ^ r := by
    rw [map_zpow, ← inv_zpow, ← mul_zpow, ← hc₀, div_eq_inv_mul]
  have h2 : ζ * (c₀ ^ r)⁻¹ * t (c₀ ^ r) = ζ ^ (s * (m' : ℤ)) := by
    rw [mul_assoc, h1]
    have e1 : s * (m' : ℤ) = 1 + (-(p : ℤ)) * r := by linarith
    rw [e1, zpow_add, zpow_one, zpow_mul, zpow_neg, zpow_natCast, inv_zpow']
  have hw : (ζ ^ (s * (m' : ℤ))) ^ p ^ e = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have : s * (m' : ℤ) * ((p ^ e : ℕ) : ℤ) = (orderOf ζ : ℤ) * s := by
      rw [hm]
      push_cast
      ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hwN : ∏ i ∈ range p, (t ^ i) (ζ ^ (s * (m' : ℤ))) = 1 := by
    simp only [map_zpow, prod_zpow, hN, one_zpow]
  rw [← mul_assoc, h2]
  exact hΩ _ (pow_eq_one_of_prod_eq_one hp hp2 ht hzp hΩ hw hwN)

end Group

end GL83.I243.Gen
