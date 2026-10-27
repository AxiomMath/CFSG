module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open QuaternionGroup

section Quat

variable {m : ℕ} [NeZero m]

theorem ii4_zmod_add_self_eq_zero (i : ZMod (2 * m)) (h : i + i = 0) : i = 0 ∨ i = (m : ZMod (2 * m)) := by
  have h1 : (2 : ZMod (2 * m)) * i = 0 := (two_mul i).trans h
  have hv : i = ((i.val : ℕ) : ZMod (2 * m)) := (ZMod.natCast_zmod_val i).symm
  rw [hv] at h1 ⊢
  have h2 : ((2 * i.val : ℕ) : ZMod (2 * m)) = 0 := by push_cast; exact h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hlt : i.val < 2 * m := ZMod.val_lt i
  obtain ⟨k, hk⟩ := h2
  have hmd : m ∣ i.val := ⟨k, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [hk]; ring)⟩
  rcases hmd with ⟨c, hc⟩
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hc2 : c < 2 := by
    have : m * c < 2 * m := by rw [← hc]; exact hlt
    nlinarith
  interval_cases c
  · left
    rw [hc]
    simp
  · right
    rw [hc]
    simp

theorem ii4_quat_sq_eq_one (x : QuaternionGroup m) (hx : x * x = 1) :
    x = 1 ∨ x = a (m : ZMod (2 * m)) := by
  cases x with
  | a i =>
    rw [a_mul_a, one_def] at hx
    rcases ii4_zmod_add_self_eq_zero i (QuaternionGroup.a.inj hx) with h | h
    · left
      rw [h]
      exact a_zero
    · right
      rw [h]
  | xa i =>
    exfalso
    rw [xa_mul_xa, one_def] at hx
    have h := QuaternionGroup.a.inj hx
    have h0 : (m : ZMod (2 * m)) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h0
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have := Nat.le_of_dvd hm h0
    omega

omit [NeZero m] in
theorem ii4_zmod_n_add_n : (m : ZMod (2 * m)) + m = 0 := by
  have : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
  push_cast at this
  linear_combination this

omit [NeZero m] in
theorem ii4_quat_a_n_central (x : QuaternionGroup m) :
    x * a (m : ZMod (2 * m)) = a (m : ZMod (2 * m)) * x := by
  have hm2 : (m : ZMod (2 * m)) + m = 0 := ii4_zmod_n_add_n
  cases x with
  | a i =>
    rw [a_mul_a, a_mul_a, add_comm]
  | xa i =>
    rw [xa_mul_a, a_mul_xa]
    congr 1
    linear_combination hm2

omit [NeZero m] in
theorem ii4_quat_noncomm (hm2 : 2 ≤ m) : ∃ x y : QuaternionGroup m, x * y ≠ y * x := by
  refine ⟨xa 0, a 1, fun h => ?_⟩
  rw [xa_mul_a, a_mul_xa] at h
  have h1 := QuaternionGroup.xa.inj h
  have h2 : (2 : ZMod (2 * m)) = 0 := by linear_combination h1
  have h3 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

end Quat

theorem exists_order_four_inverted {P : Type} [Group P] {n : ℕ} (hP : IVK.IsQuaternionTwoGroup P n)
    (φ : MulAut P) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) : ∃ w : P, orderOf w = 4 ∧ φ w = w⁻¹ := by
  classical
  obtain ⟨hn3, ⟨e⟩⟩ := hP
  have hm : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  set m := 2 ^ (n - 2) with hmdef
  have hcard : Nat.card P = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, hmdef]
    have hn : n = (n - 2) + 2 := by omega
    conv_rhs => rw [hn, pow_add]
    ring
  have hp2 : IsPGroup 2 P := IsPGroup.of_card hcard
  by_contra hcon
  push Not at hcon
  set u : P := e.symm (a (m : ZMod (2 * m))) with hu
  have hucen : ∀ g : P, g * u = u * g := fun g => e.injective (by
    rw [map_mul, map_mul, hu, MulEquiv.apply_symm_apply]
    exact ii4_quat_a_n_central (e g))
  have hinv : ∀ x : P, x * x = 1 → x = 1 ∨ x = u := by
    intro x hx
    rcases ii4_quat_sq_eq_one (e x) (by rw [← map_mul, hx, map_one]) with h | h
    · left
      exact e.injective (by rw [h, map_one])
    · right
      exact e.injective (by rw [h, hu, MulEquiv.apply_symm_apply])
  have hu2 : u * u = 1 := e.injective (by
    rw [map_mul, hu, MulEquiv.apply_symm_apply, a_mul_a, ii4_zmod_n_add_n, map_one]
    exact a_zero)
  have key : ∀ g : P, φ g = g ∨ φ g = u * g := by
    intro g
    have hφφ : φ (φ g) = g := by
      have := congrArg (fun ρ : MulAut P => ρ g) hφ2
      simpa using this
    set w : P := g * (φ g)⁻¹ with hw
    have hφw : φ w = w⁻¹ := by
      rw [hw, map_mul, map_inv, hφφ]
      group
    have hw2 : w * w = 1 := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hp2) w
      by_contra hne
      have hj2 : 2 ≤ j := by
        by_contra hlt
        apply hne
        have hj1 : j ≤ 1 := by omega
        have h2 : w ^ 2 = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one, hj]
          calc 2 ^ j ∣ 2 ^ 1 := pow_dvd_pow 2 hj1
            _ = 2 := pow_one 2
        rwa [pow_two] at h2
      have h4 : orderOf (w ^ 2 ^ (j - 2)) = 4 := by
        rw [orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact pow_dvd_pow 2 (by omega)), hj]
        have h3 : 2 ^ j = 2 ^ (j - 2) * 4 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
        rw [h3, Nat.mul_div_cancel_left _ (by positivity)]
      exact hcon _ h4 (by rw [map_pow, hφw, inv_pow])
    rcases hinv w hw2 with h | h
    · left
      have h' : g * (φ g)⁻¹ = 1 := h
      exact (mul_inv_eq_one.1 h').symm
    · right
      have h' : g * (φ g)⁻¹ = u := h
      have h'' : φ g = u⁻¹ * g := by
        calc φ g = (g * (φ g)⁻¹)⁻¹ * g := by group
          _ = u⁻¹ * g := by rw [h']
      rw [h'', inv_eq_of_mul_eq_one_right hu2]
  have hfix4 : ∀ g : P, orderOf g = 4 → φ g = g := by
    intro g hg
    have hg4 : g ^ 4 = 1 := by
      rw [← hg]
      exact pow_orderOf_eq_one g
    rcases key g with h | h
    · exact h
    · exfalso
      have hsq : g * g = u := by
        have h1 : (g * g) * (g * g) = 1 := by
          calc (g * g) * (g * g) = g ^ 4 := by simp [pow_succ, mul_assoc]
            _ = 1 := hg4
        rcases hinv (g * g) h1 with h2 | h2
        · exfalso
          have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
          rw [hg] at h3
          omega
        · exact h2
      have hginv : g⁻¹ = g * g * g := by
        apply inv_eq_of_mul_eq_one_right
        calc g * (g * g * g) = g ^ 4 := by simp [pow_succ, mul_assoc]
          _ = 1 := hg4
      exact hcon g hg (by rw [h, ← hsq, hginv])
  have hord4 : ∀ i : ZMod (2 * m), orderOf (e.symm (xa i)) = 4 := fun i => by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_xa i
  have hfixall : ∀ x : P, φ x = x := by
    intro x
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    cases y with
    | xa i => exact hfix4 _ (hord4 i)
    | a k =>
      have hprod : e.symm (a k) = e.symm (xa 0) * e.symm (xa (k - (m : ZMod (2 * m)))) := by
        rw [← map_mul, xa_mul_xa]
        congr 2
        ring
      rw [hprod, map_mul, hfix4 _ (hord4 0), hfix4 _ (hord4 _)]
  apply hφ1
  ext x
  rw [hfixall x]
  rfl

end CFSG.GH74.GLS.IVK.Lifted
