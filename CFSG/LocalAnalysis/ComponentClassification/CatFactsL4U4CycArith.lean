module

public import Mathlib.NumberTheory.Multiplicity
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Cyc

theorem padicValNat_add_le {x j : ℕ} (hx1 : 1 < x) (hx : Odd x) (hj : 1 ≤ j) :
    padicValNat 2 (x + 1) + j ≤ padicValNat 2 (x ^ 2 ^ j - 1) ∧
      padicValNat 2 (x - 1) + j ≤ padicValNat 2 (x ^ 2 ^ j - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : ¬ 2 ∣ x := fun h => (Nat.not_even_iff_odd.mpr hx) (even_iff_two_dvd.mpr h)
  have hev : Even (2 ^ j) := (Nat.even_pow' (by omega)).mpr even_two
  have h := padicValNat.pow_two_sub_one hx1 hx2 (pow_ne_zero j two_ne_zero) hev
  rw [padicValNat.prime_pow] at h
  obtain ⟨k, rfl⟩ := hx
  have h1 : 1 ≤ padicValNat 2 (2 * k + 1 + 1) :=
    one_le_padicValNat_of_dvd (by omega) ⟨k + 1, by ring⟩
  have h2 : 1 ≤ padicValNat 2 (2 * k + 1 - 1) :=
    one_le_padicValNat_of_dvd (by omega) ⟨k, by omega⟩
  omega

theorem padicValNat_sq_add_one {x : ℕ} (hx : Odd x) : padicValNat 2 (x ^ 2 + 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hx
  have e : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
  rw [e, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by omega)]

theorem three_le_padicValNat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    3 ≤ padicValNat 2 (p + 1) + padicValNat 2 (p - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h1 : 2 ≤ padicValNat 2 (p - 1) :=
      (padicValNat_dvd_iff_le (by omega)).mp ⟨m, by rw [hk, hm]; ring_nf; omega⟩
    have h2 : 1 ≤ padicValNat 2 (p + 1) := one_le_padicValNat_of_dvd (by omega) ⟨k + 1, by omega⟩
    omega
  · have h1 : 2 ≤ padicValNat 2 (p + 1) :=
      (padicValNat_dvd_iff_le (by omega)).mp ⟨m + 1, by rw [hk, hm]; ring⟩
    have h2 : 1 ≤ padicValNat 2 (p - 1) := one_le_padicValNat_of_dvd (by omega) ⟨k, by omega⟩
    omega

theorem padicValNat_two_mul_add_two_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    padicValNat 2 (2 * f) + 2 ≤ padicValNat 2 (p ^ (2 * f) - 1) := by
  have hx2 : ¬ 2 ∣ p := fun h =>
    (Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hp2)) (even_iff_two_dvd.mpr h)
  have h := padicValNat.pow_two_sub_one hp.one_lt hx2 (by omega : 2 * f ≠ 0) (even_two_mul f)
  have h3 := three_le_padicValNat hp hp2
  omega

theorem two_pow_mul_le {p f d j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hd : d * 2 ^ j = 2 * f) :
    2 ^ padicValNat 2 (p ^ d - 1) * 2 ^ j ≤ 2 ^ padicValNat 2 (p ^ (2 * f) - 1) ∧
      2 ^ padicValNat 2 (p ^ d + 1) * 2 ^ j ≤ 2 ^ padicValNat 2 (p ^ (2 * f) - 1) := by
  rw [← pow_add, ← pow_add]
  have h22 := padicValNat_two_mul_add_two_le hp hp2 hf
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, mul_one] at hd
    subst hd
    refine ⟨le_rfl, Nat.pow_le_pow_right (by norm_num) ?_⟩
    have h1 : padicValNat 2 (p ^ (2 * f) + 1) = 1 := by
      rw [show p ^ (2 * f) = (p ^ f) ^ 2 by ring]
      exact padicValNat_sq_add_one (hp.odd_of_ne_two hp2).pow
    omega
  · have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, zero_mul] at hd; omega
      · exact h0
    have hx1 : 1 < p ^ d := Nat.one_lt_pow hd0.ne' hp.one_lt
    have hQ : p ^ (2 * f) = (p ^ d) ^ 2 ^ j := by rw [← pow_mul, hd]
    obtain ⟨h1, h2⟩ := padicValNat_add_le hx1 ((hp.odd_of_ne_two hp2).pow) hj
    rw [hQ]
    exact ⟨Nat.pow_le_pow_right (by norm_num) h2, Nat.pow_le_pow_right (by norm_num) h1⟩

theorem four_mul_le {p f j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hj : 2 ^ j ∣ 2 * f) : 4 * 2 ^ j ≤ 2 ^ padicValNat 2 (p ^ (2 * f) - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : j ≤ padicValNat 2 (2 * f) := (padicValNat_dvd_iff_le (by omega)).mp hj
  have h22 := padicValNat_two_mul_add_two_le hp hp2 hf
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_dvd_of_forall_pow_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (B : Subgroup G) {n : ℕ} (h : ∀ b ∈ B, b ^ n = 1) : Nat.card B ∣ n := by
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one fun b => Subtype.ext (by simpa using h b b.2)

theorem frob_pow_apply {K : Type*} [Field K] {p : ℕ} {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ p)
    (n : ℕ) (c : K) : (φ ^ n) c = c ^ p ^ n := by
  induction n with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]

theorem exists_frob_pow_mem {K : Type} [Field K] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = p ^ n) (Γ : Subgroup (K ≃+* K)) :
    ∃ d : ℕ, d * Nat.card Γ = n ∧ ∃ ψ ∈ Γ, ∀ c, ψ c = c ^ p ^ d := by
  obtain ⟨φ, hφ, hord, hzp, hcard, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hn hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hcyc : IsCyclic (K ≃+* K) := ⟨⟨φ, fun x => by
    have : x ∈ Subgroup.zpowers φ := by rw [hzp]; exact Subgroup.mem_top x
    exact this⟩⟩
  have hΓ : Nat.card Γ ∣ n := hcard ▸ Subgroup.card_subgroup_dvd_card Γ
  obtain ⟨d, hd⟩ := hΓ
  have hΓ0 : 0 < Nat.card Γ := Nat.card_pos
  have hd0 : d ≠ 0 := by rintro rfl; omega
  refine ⟨d, by rw [hd, mul_comm], φ ^ d, ?_, frob_pow_apply hφ d⟩
  have hordψ : orderOf (φ ^ d) = Nat.card Γ := by
    rw [orderOf_pow_of_dvd hd0 (by rw [hord, hd]; exact dvd_mul_left d _), hord, hd,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
  have heq : Subgroup.zpowers (φ ^ d) = Γ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, hordψ]
  rw [← heq]
  exact Subgroup.mem_zpowers _

end L2Cyc

end CFSG.ComponentClassification.CatFactsL4U4
