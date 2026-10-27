module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Wreathed.BrauerWreathedOrder

theorem odd_orderOf_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {d : ℕ} (hd : Odd d)
    (h : x ^ d = 1) : Odd (orderOf x) :=
  hd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h)

theorem exists_eq_sq_of_odd_orderOf {M : Type*} [Monoid M] {w : M} (hw : Odd (orderOf w)) :
    ∃ z : M, Odd (orderOf z) ∧ w = z ^ 2 := by
  obtain ⟨k, hk⟩ := hw
  refine ⟨w ^ (k + 1), odd_orderOf_of_pow_eq_one (d := orderOf w) ⟨k, hk⟩ ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [← pow_mul, show (k + 1) * 2 = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]

variable {F : Type} [Field F] [Fintype F] {n d : ℕ}

theorem units_pow_card_sub_one (x : Fˣ) : x ^ (Fintype.card F - 1) = 1 := by
  classical
  rw [← Fintype.card_units]
  exact pow_card_eq_one

theorem odd_orderOf_pow_two_pow (hqd : Fintype.card F - 1 = 2 ^ n * d) (hd : Odd d)
    (c : Fˣ) : Odd (orderOf (c ^ 2 ^ n)) := by
  apply odd_orderOf_of_pow_eq_one hd
  rw [← pow_mul, ← hqd, units_pow_card_sub_one]

theorem card_div_two_eq (hqd : Fintype.card F - 1 = 2 ^ n * d) (hn : 1 ≤ n) :
    Fintype.card F / 2 = 2 ^ (n - 1) * d := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hq : 0 < Fintype.card F := Fintype.card_pos
  rw [h2, mul_assoc] at hqd
  omega

theorem nonsquare_pow_card_div_two (hF : ringChar F ≠ 2) {c : Fˣ} (hc : ¬ IsSquare c) :
    c ^ (Fintype.card F / 2) = -1 := by
  rcases FiniteField.pow_dichotomy hF (Units.ne_zero c) with h | h
  · exact absurd ((FiniteField.unit_isSquare_iff hF c).mpr (Units.ext (by simpa using h))) hc
  · exact Units.ext (by simpa using h)

theorem exists_pow_two_pow_pred_eq_neg (hF : ringChar F ≠ 2)
    (hqd : Fintype.card F - 1 = 2 ^ n * d) (hd : Odd d) (hn : 1 ≤ n) {c : Fˣ}
    (hc : ¬ IsSquare c) : ∃ u : Fˣ, Odd (orderOf u) ∧ c ^ 2 ^ (n - 1) = -u := by
  refine ⟨-(c ^ 2 ^ (n - 1)), odd_orderOf_of_pow_eq_one hd ?_, (neg_neg _).symm⟩
  rw [neg_pow, ← pow_mul, ← card_div_two_eq hqd hn, nonsquare_pow_card_div_two hF hc,
    hd.neg_one_pow, neg_one_mul, neg_neg]

theorem exists_odd_pow_eq_of_nonsquare {γ : Fˣ} (hγ : ∀ x : Fˣ, x ∈ Subgroup.zpowers γ)
    {c : Fˣ} (hc : ¬ IsSquare c) : ∃ i : ℕ, Odd i ∧ c = γ ^ i := by
  obtain ⟨i, hi⟩ : c ∈ Submonoid.powers γ := (mem_powers_iff_mem_zpowers).mpr (hγ c)
  dsimp only at hi
  refine ⟨i, ?_, hi.symm⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, rfl⟩ := hodd
  exact hc ⟨γ ^ k, by rw [← hi, pow_add]⟩

theorem two_pow_dvd_of_odd_orderOf_pow (hqd : Fintype.card F - 1 = 2 ^ n * d) {c : Fˣ}
    (hc : ¬ IsSquare c) {j : ℕ} (hj : Odd (orderOf (c ^ j))) : 2 ^ n ∣ j := by
  classical
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hγo : orderOf γ = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨i, hi, rfl⟩ := exists_odd_pow_eq_of_nonsquare hγ hc
  have h1 : γ ^ (i * j * orderOf ((γ ^ i) ^ j)) = 1 := by
    rw [mul_assoc, pow_mul, pow_mul, pow_orderOf_eq_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hγo, hqd] at h2
  have h3 : 2 ^ n ∣ j * (i * orderOf ((γ ^ i) ^ j)) := by
    have := dvd_trans (dvd_mul_right (2 ^ n) d) h2
    rwa [show i * j * orderOf ((γ ^ i) ^ j) = j * (i * orderOf ((γ ^ i) ^ j)) by ring] at this
  exact (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (hi.mul hj))).dvd_of_dvd_mul_right h3

theorem exists_eq_pow_mul_odd (hqd : Fintype.card F - 1 = 2 ^ n * d) (hd : Odd d) {c : Fˣ}
    (hc : ¬ IsSquare c) (y : Fˣ) : ∃ (k : ℕ) (w : Fˣ), Odd (orderOf w) ∧ y = c ^ k * w := by
  classical
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hγo : orderOf γ = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨i, hi, rfl⟩ := exists_odd_pow_eq_of_nonsquare hγ hc
  obtain ⟨t, ht⟩ : y ∈ Submonoid.powers γ := (mem_powers_iff_mem_zpowers).mpr (hγ y)
  dsimp only at ht
  subst ht
  have hcop : Nat.Coprime i (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hi)
  let u : ZMod (2 ^ n) := (t : ZMod (2 ^ n)) * (i : ZMod (2 ^ n))⁻¹
  refine ⟨u.val, ((γ ^ i) ^ u.val)⁻¹ * γ ^ t, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hmod : i * u.val ≡ t [MOD 2 ^ n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    change (i : ZMod (2 ^ n)) * ((t : ZMod (2 ^ n)) * (i : ZMod (2 ^ n))⁻¹) = t
    rw [mul_comm (t : ZMod (2 ^ n)), ← mul_assoc, ZMod.coe_mul_inv_eq_one i hcop, one_mul]
  have hmod' : i * u.val * d ≡ t * d [MOD 2 ^ n * d] := Nat.ModEq.mul_right' d hmod
  apply odd_orderOf_of_pow_eq_one hd
  have hpow : (γ ^ i) ^ u.val = γ ^ (i * u.val) := by rw [pow_mul]
  rw [hpow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, inv_mul_eq_one,
    pow_eq_pow_iff_modEq, hγo, hqd]
  exact hmod'

end CFSG.Wreathed.BrauerWreathedOrder
