module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open Equiv

theorem quaternion_center_ne_one {n : ℕ} (hn : n ≠ 0) :
    (QuaternionGroup.a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := by
  intro h
  rw [QuaternionGroup.one_def] at h
  have h' := QuaternionGroup.a.inj h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h'
  omega

theorem quaternion_involution_eq {n : ℕ} (hn : n ≠ 0) {h : QuaternionGroup n}
    (h2 : orderOf h = 2) : h = QuaternionGroup.a (n : ZMod (2 * n)) := by
  have : NeZero n := ⟨hn⟩
  cases h with
  | xa i => rw [QuaternionGroup.orderOf_xa] at h2; omega
  | a i =>
    have hsq : (QuaternionGroup.a i : QuaternionGroup n) ^ 2 = 1 := by
      rw [← h2]
      exact pow_orderOf_eq_one _
    have hi : 2 * i = 0 := by
      rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at hsq
      have := QuaternionGroup.a.inj hsq
      linear_combination this
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [← QuaternionGroup.one_def, orderOf_one] at h2
      omega
    have hn2 : 2 * (n : ZMod (2 * n)) = 0 := by
      have : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
      push_cast at this
      exact this
    have hn0 : (n : ZMod (2 * n)) ≠ 0 := by
      have h1 := quaternion_center_ne_one hn
      intro h
      apply h1
      rw [h, QuaternionGroup.one_def]
    rw [zmod_eq_of_two_mul_eq_zero' hi hn2 hi0 hn0]

theorem quaternion_exists_pow_eq {k : ℕ} {g : QuaternionGroup (2 ^ k)} (hg : g ≠ 1) :
    ∃ m : ℕ, g ^ m = QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
  have hn : 2 ^ k ≠ 0 := by positivity
  have : NeZero (2 ^ k) := ⟨hn⟩
  have hcard : Nat.card (QuaternionGroup (2 ^ k)) = 2 ^ (k + 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hdvd : orderOf g ∣ 2 ^ (k + 2) := hcard ▸ orderOf_dvd_natCard g
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hg (orderOf_eq_one_iff.mp (by simpa using hj))
  have h2 : 2 ∣ orderOf g := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  refine ⟨orderOf g / 2, quaternion_involution_eq hn ?_⟩
  exact orderOf_pow_orderOf_div (by rw [hj]; positivity) h2

theorem quaternion_not_injective_perm {k n : ℕ} (hk : 1 ≤ k) (hn : n < 8)
    (φ : QuaternionGroup (2 ^ k) →* Perm (Fin n)) (hφ : Function.Injective φ) : False := by
  classical
  have h0 : 2 ^ k ≠ 0 := by positivity
  have : NeZero (2 ^ k) := ⟨h0⟩
  let z := (QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) : QuaternionGroup (2 ^ k))
  have hz : φ z ≠ 1 := by
    intro h
    exact quaternion_center_ne_one h0 (hφ (h.trans (map_one φ).symm))
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ z x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hz (Equiv.ext h)
  have hinj : Function.Injective (fun g : QuaternionGroup (2 ^ k) => φ g x₀) := by
    intro g h hgh
    simp only at hgh
    by_contra hne
    have h1 : h⁻¹ * g ≠ 1 := by
      intro h1
      apply hne
      calc g = h * (h⁻¹ * g) := by group
        _ = h := by rw [h1, mul_one]
    obtain ⟨m, hm⟩ := quaternion_exists_pow_eq h1
    have hm' : (h⁻¹ * g) ^ m = z := hm
    have hfix : φ (h⁻¹ * g) x₀ = x₀ := by
      rw [map_mul, Perm.mul_apply, hgh, map_inv]
      simp
    have hpow : ∀ j : ℕ, (φ (h⁻¹ * g) ^ j) x₀ = x₀ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, Perm.mul_apply, hfix, ih]
    apply hx₀
    rw [← hm', map_pow]
    exact hpow m
  have hle := Fintype.card_le_of_injective _ hinj
  rw [QuaternionGroup.card, Fintype.card_fin] at hle
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem quaternion_pair (k : ℕ) (hk : 1 ≤ k) :
    orderOf (QuaternionGroup.a ((2 ^ (k - 1) : ℕ) : ZMod (2 * 2 ^ k)) :
      QuaternionGroup (2 ^ k)) = 4 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) ^ 2 =
      (QuaternionGroup.a ((2 ^ (k - 1) : ℕ) : ZMod (2 * 2 ^ k))) ^ 2 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) *
      QuaternionGroup.a ((2 ^ (k - 1) : ℕ) : ZMod (2 * 2 ^ k)) *
      (QuaternionGroup.xa 0)⁻¹ =
      (QuaternionGroup.a ((2 ^ (k - 1) : ℕ) : ZMod (2 * 2 ^ k)))⁻¹ := by
  have h0 : 2 ^ k ≠ 0 := by positivity
  have : NeZero (2 ^ k) := ⟨h0⟩
  have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [QuaternionGroup.orderOf_a, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      rw [hk']
      have : 0 < 2 ^ (k - 1) := by positivity
      omega)]
    rw [hk']
    have : 0 < 2 ^ (k - 1) := by positivity
    rw [show 2 * (2 * 2 ^ (k - 1)) = 2 ^ (k - 1) * 4 by ring, Nat.gcd_mul_right_left]
    rw [Nat.mul_div_cancel_left _ this]
  · rw [QuaternionGroup.xa_sq, pow_two, QuaternionGroup.a_mul_a]
    congr 1
    rw [← Nat.cast_add, ← two_mul, ← hk']
  · have h2n : ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by
      rw [← Nat.cast_add, ← two_mul]
      exact ZMod.natCast_self _
    have hinva : ∀ i : ZMod (2 * 2 ^ k),
        (QuaternionGroup.a i : QuaternionGroup (2 ^ k))⁻¹ = QuaternionGroup.a (-i) := by
      intro i
      apply inv_eq_of_mul_eq_one_right
      rw [QuaternionGroup.a_mul_a, add_neg_cancel, QuaternionGroup.a_zero]
    have hinvx : (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k))⁻¹ =
        QuaternionGroup.xa ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
      apply inv_eq_of_mul_eq_one_right
      rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.one_def, sub_zero, h2n]
    rw [QuaternionGroup.xa_mul_a, hinva, hinvx, QuaternionGroup.xa_mul_xa]
    congr 1
    linear_combination h2n

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
