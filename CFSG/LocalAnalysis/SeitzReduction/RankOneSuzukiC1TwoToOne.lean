module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRadical

public section

namespace CFSG.SeitzReduction.RankOne

namespace SzC1

open SzRadical

variable {K : Type*} [Field K]

theorem partner_identity [CharP K 2] (c s β b : K) :
    s ^ 2 * (c ^ 2 * s ^ 2 + b ^ 2 * c + β ^ 2) ^ 2 +
      b ^ 2 * c * (c * s ^ 2 + β * s + b ^ 2) ^ 2 + β ^ 2 * b ^ 4 +
      (c * s ^ 2 + β * s + b ^ 2) ^ 2 * (c ^ 2 * s ^ 2 + b ^ 2 * c + β ^ 2) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (β ^ 2 * b ^ 4 + s * β ^ 3 * b ^ 2 + s ^ 2 * β ^ 4 + c * b ^ 6 +
    2 * c * s * β * b ^ 4 + 3 * c * s ^ 2 * β ^ 2 * b ^ 2 + c * s ^ 3 * β ^ 3 +
    3 * c ^ 2 * s ^ 2 * b ^ 4 + 3 * c ^ 2 * s ^ 3 * β * b ^ 2 + 2 * c ^ 2 * s ^ 4 * β ^ 2 +
    3 * c ^ 3 * s ^ 4 * b ^ 2 + c ^ 3 * s ^ 5 * β + c ^ 4 * s ^ 6) * h2

theorem pow_theta_eq_sq {a : ℕ} (x : K) : x ^ 2 ^ (a + 1) = (x ^ 2 ^ a) ^ 2 := by
  rw [← pow_mul, pow_succ]

variable [Fintype K] [CharP K 2] {a : ℕ}

theorem pow_theta_add_add_one_ne_zero (hK : Fintype.card K = 2 ^ (2 * a + 1)) (x : K) :
    x ^ 2 ^ (a + 1) + x + 1 ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro h
  have h1 : x ^ 2 ^ (a + 1) = x + 1 := by linear_combination h - (x + 1) * h2
  have hsq : x ^ 2 = x := by
    have e := pow_theta_pow_theta hK x
    rw [h1, frob_add, h1, one_pow] at e
    linear_combination -e + h2
  have hx : x * (x - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hx with h0 | h0
  · rw [h0, zero_pow (two_pow_ne_zero _), zero_add, zero_add] at h
    exact one_ne_zero h
  · have hx1 : x = 1 := sub_eq_zero.mp h0
    rw [hx1, one_pow] at h
    exact one_ne_zero (by linear_combination h - h2)

omit [CharP K 2] in
theorem partnerDen_eq (hK : Fintype.card K = 2 ^ (2 * a + 1)) (β : K) {c : K} (hc : c ≠ 0) :
    c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a + β ^ 2 ^ (a + 1) =
      c ^ (2 ^ (a + 1) + 1) * ((β / (c ^ 2 ^ a * c)) ^ 2 ^ (a + 1) + β / (c ^ 2 ^ a * c) + 1) := by
  have hs : c ^ 2 ^ a ≠ 0 := pow_ne_zero _ hc
  rw [div_pow, mul_pow, pow_sigma_pow_theta hK, pow_succ c (2 ^ (a + 1)), pow_theta_eq_sq c]
  field_simp
  ring

theorem partnerDen_ne_zero (hK : Fintype.card K = 2 ^ (2 * a + 1)) {β : K} (hβ : β ≠ 0) (c : K) :
    c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a + β ^ 2 ^ (a + 1) ≠ 0 := by
  by_cases hc : c = 0
  · rw [hc, zero_pow (Nat.succ_ne_zero _), zero_pow (two_pow_ne_zero _), mul_zero, zero_add,
      zero_add]
    exact pow_ne_zero _ hβ
  rw [partnerDen_eq hK β hc]
  exact mul_ne_zero (pow_ne_zero _ hc) (pow_theta_add_add_one_ne_zero hK _)

theorem partner_spec (hK : Fintype.card K = 2 ^ (2 * a + 1)) {β : K} (hβ : β ≠ 0) (c : K) :
    β ^ (2 ^ (a + 1) + 2) / (c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a + β ^ 2 ^ (a + 1)) ^ 2 ≠ 0 ∧
      (c + β ^ (2 ^ (a + 1) + 2) /
          (c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a + β ^ 2 ^ (a + 1)) ^ 2) ^ (2 ^ (a + 1) + 1) +
        β * (c + β ^ (2 ^ (a + 1) + 2) /
          (c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a + β ^ 2 ^ (a + 1)) ^ 2) ^ 2 ^ a =
      c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a := by
  have hD := partnerDen_ne_zero hK hβ c
  set D := c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a + β ^ 2 ^ (a + 1) with hDdef
  set e := β ^ (2 ^ (a + 1) + 2) / D ^ 2 with hedef
  refine ⟨div_ne_zero (pow_ne_zero _ hβ) (pow_ne_zero _ hD), ?_⟩
  set s := c ^ 2 ^ a with hs
  set b := β ^ 2 ^ a with hb
  have hcθ : c ^ 2 ^ (a + 1) = s ^ 2 := pow_theta_eq_sq c
  have hβθ : β ^ 2 ^ (a + 1) = b ^ 2 := pow_theta_eq_sq β
  have hsθ : s ^ 2 ^ (a + 1) = c := pow_sigma_pow_theta hK c
  have hbθ : b ^ 2 ^ (a + 1) = β := pow_sigma_pow_theta hK β
  have hD' : D = c * s ^ 2 + β * s + b ^ 2 := by
    rw [hDdef, pow_succ, hcθ, hβθ]
    ring
  set D' := c ^ 2 * s ^ 2 + b ^ 2 * c + β ^ 2 with hD'def
  have hDθ : D ^ 2 ^ (a + 1) = D' := by
    rw [hD', frob_add, frob_add, mul_pow, mul_pow, pow_right_comm s 2, pow_right_comm b 2, hsθ,
      hcθ, hβθ, hbθ]
    ring
  have hDσ2 : (D ^ 2 ^ a) ^ 2 = D' := by rw [← pow_theta_eq_sq, hDθ]
  have hD'0 : D' ≠ 0 := by
    rw [← hDθ]
    exact pow_ne_zero _ hD
  have he : e = b ^ 2 * β ^ 2 / D ^ 2 := by
    rw [hedef, pow_add, hβθ]
  have heθ : e ^ 2 ^ (a + 1) = β ^ 2 * b ^ 4 / D' ^ 2 := by
    rw [hedef, div_pow, pow_right_comm D 2, hDθ, pow_add, hβθ, mul_pow, pow_right_comm b 2,
      pow_right_comm β 2, hbθ, hβθ]
    ring
  have heσ : e ^ 2 ^ a = β * b ^ 2 / D' := by
    rw [hedef, div_pow, pow_right_comm D 2, hDσ2, pow_add, mul_pow, pow_theta_pow_sigma hK,
      pow_right_comm β 2]
  have key : c ^ 2 ^ (a + 1) * e + e ^ 2 ^ (a + 1) * c + e ^ 2 ^ (a + 1) * e +
      β * e ^ 2 ^ a = 0 := by
    have hexp : c ^ 2 ^ (a + 1) * e + e ^ 2 ^ (a + 1) * c + e ^ 2 ^ (a + 1) * e +
        β * e ^ 2 ^ a = β ^ 2 * b ^ 2 / (D ^ 2 * D' ^ 2) * (s ^ 2 * D' ^ 2 +
          b ^ 2 * c * D ^ 2 + β ^ 2 * b ^ 4 + D ^ 2 * D') := by
      rw [hcθ, heθ, heσ, he]
      field_simp
    rw [hexp, hD', hD'def, partner_identity, mul_zero]
  rw [pow_succ (c + e), pow_succ c, frob_add, frob_add]
  linear_combination key

end SzC1

theorem sz_two_to_one {K : Type*} [Field K] [Fintype K] [CharP K 2] {a : ℕ} (_ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {β : K} (hβ : β ≠ 0) (c : K) :
    ∃ e : K, e ≠ 0 ∧ (c + e) ^ (2 ^ (a + 1) + 1) + β * (c + e) ^ 2 ^ a =
      c ^ (2 ^ (a + 1) + 1) + β * c ^ 2 ^ a :=
  ⟨_, SzC1.partner_spec hK hβ c⟩

end CFSG.SeitzReduction.RankOne
