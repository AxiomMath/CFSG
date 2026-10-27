module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Basic

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

namespace Rel

variable {a b a' b' t : G} {M : ℕ}

theorem two_mul_pos (h : Rel a b a' b' t M) : 0 < 2 * M := by have := h.one_le; omega

theorem not_dvd_of_lt {m : ℕ} (hm : 0 < m) (hlt : m < 2 * M) : ¬ (((2 * M : ℕ) : ℤ) ∣ (m : ℤ)) := by
  intro hd
  have := Int.le_of_dvd (by exact_mod_cast hm) hd
  omega

theorem commute_a_a' (h : Rel a b a' b' t M) : Commute a a' := h.c_aa

theorem dl1_zpow (h : Rel a b a' b' t M) (k : ℤ) : (a * a'⁻¹) ^ k = a ^ k * a' ^ (-k) := by
  rw [Commute.mul_zpow (h.commute_a_a'.inv_right) k, inv_zpow']

theorem dl2_zpow (h : Rel a b a' b' t M) (k : ℤ) : (a * a') ^ k = a ^ k * a' ^ k :=
  Commute.mul_zpow h.commute_a_a' k

theorem orderOf_dl2 (h : Rel a b a' b' t M) : orderOf (a * a') = 2 * M := by
  rw [orderOf_eq_iff h.two_mul_pos]
  refine ⟨?_, fun m hm hm0 hm1 => ?_⟩
  · rw [Commute.mul_pow h.commute_a_a', h.z_eq]
    exact h.aN_sq
  · have h1 : (a * a') ^ (m : ℤ) = 1 := by rw [zpow_natCast]; exact hm1
    rw [h.dl2_zpow] at h1
    have h2 : a ^ (m : ℤ) = a' ^ (-(m : ℤ)) := by
      rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1
    exact not_dvd_of_lt hm0 hm (h.dvd_of_zpow_eq_a h2)

theorem orderOf_dl1 (h : Rel a b a' b' t M) : orderOf (a * a'⁻¹) = 2 * M := by
  rw [orderOf_eq_iff h.two_mul_pos]
  refine ⟨?_, fun m hm hm0 hm1 => ?_⟩
  · rw [Commute.mul_pow (h.commute_a_a'.inv_right), inv_pow, h.z_eq, mul_inv_cancel]
  · have h1 : (a * a'⁻¹) ^ (m : ℤ) = 1 := by rw [zpow_natCast]; exact hm1
    rw [h.dl1_zpow] at h1
    have h2 : a ^ (m : ℤ) = a' ^ (m : ℤ) := by
      have := eq_inv_of_mul_eq_one_left h1
      rw [zpow_neg, inv_inv] at this
      exact this
    exact not_dvd_of_lt hm0 hm (h.dvd_of_zpow_eq_a h2)

theorem t_dl1 (h : Rel a b a' b' t M) : t * (a * a'⁻¹) * t⁻¹ = (a * a'⁻¹)⁻¹ := by
  have h1 : t * a * t⁻¹ = a' := by rw [h.t_inv]; exact h.tat
  have h2 : t * a'⁻¹ * t⁻¹ = a⁻¹ := by
    have : t * a' * t⁻¹ = a := by
      rw [h.t_inv, h.ta', mul_assoc, h.t_sq, mul_one]
    calc t * a'⁻¹ * t⁻¹ = (t * a' * t⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [this]
  calc t * (a * a'⁻¹) * t⁻¹ = (t * a * t⁻¹) * (t * a'⁻¹ * t⁻¹) := by group
    _ = a' * a⁻¹ := by rw [h1, h2]
    _ = (a * a'⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]

theorem one_lt_two_mul (h : Rel a b a' b' t M) : 1 < 2 * M := by have := h.one_le; omega

theorem a_ne_a' (h : Rel a b a' b' t M) : a ≠ a' := by
  intro e
  have : a ^ (1 : ℤ) = a' ^ (1 : ℤ) := by rw [zpow_one, zpow_one, e]
  exact not_dvd_of_lt (m := 1) (by norm_num) h.one_lt_two_mul (h.dvd_of_zpow_eq_a this)

theorem a_ne_a'_inv (h : Rel a b a' b' t M) : a ≠ a'⁻¹ := by
  intro e
  have : a ^ (1 : ℤ) = a' ^ (-1 : ℤ) := by rw [zpow_one, zpow_neg_one, e]
  exact not_dvd_of_lt (m := 1) (by norm_num) h.one_lt_two_mul (h.dvd_of_zpow_eq_a this)

theorem commute_a_A (h : Rel a b a' b' t M) (i j : ℤ) : Commute a (a ^ i * a' ^ j) :=
  Commute.mul_right (Commute.zpow_right (Commute.refl a) i) (Commute.zpow_right h.commute_a_a' j)

theorem t_not_mem_dl1 (h : Rel a b a' b' t M) : t ∉ zpowers (a * a'⁻¹) := by
  intro ht
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ht
  rw [h.dl1_zpow] at hk
  have hc : Commute a t := by rw [← hk]; exact h.commute_a_A k (-k)
  have h1 : a' * t = a * t := by rw [← h.ta]; exact hc.eq.symm
  exact h.a_ne_a' (mul_right_cancel h1).symm

theorem s2_sq (h : Rel a b a' b' t M) : (b * b' * t) * (b * b' * t) = 1 := by
  calc (b * b' * t) * (b * b' * t) = (b * b') * (t * (b * b')) * t := by simp only [mul_assoc]
    _ = (b * b') * ((b * b') * t) * t := by rw [h.t_b0]
    _ = ((b * b') * (b * b')) * (t * t) := by simp only [mul_assoc]
    _ = 1 := by rw [h.b0_sq, h.t_sq, mul_one]

theorem s2_inv (h : Rel a b a' b' t M) : (b * b' * t)⁻¹ = b * b' * t :=
  inv_eq_of_mul_eq_one_right h.s2_sq

theorem b0_inv (h : Rel a b a' b' t M) : (b * b')⁻¹ = b * b' := inv_eq_of_mul_eq_one_right h.b0_sq

theorem s2_dl2 (h : Rel a b a' b' t M) : (b * b' * t) * (a * a') * (b * b' * t)⁻¹ = (a * a')⁻¹ := by
  rw [h.s2_inv]
  have h1 : t * (a * a') * t = a * a' := by
    calc t * (a * a') * t = (t * a * t) * (t * a' * t) := by
          calc t * (a * a') * t = t * a * (t * t) * a' * t := by rw [h.t_sq]; simp only [mul_assoc, mul_one]
            _ = (t * a * t) * (t * a' * t) := by simp only [mul_assoc]
      _ = a' * a := by
          rw [h.tat]
          have : t * a' * t = a := by rw [h.ta', mul_assoc, h.t_sq, mul_one]
          rw [this]
      _ = a * a' := h.c_aa.symm
  have h2 : (b * b') * (a * a') * (b * b') = (a * a')⁻¹ := by
    have e1 : (b * b') * a = a⁻¹ * (b * b') := by simpa using h.b0_zpow_a 1
    have e2 : (b * b') * a' = a'⁻¹ * (b * b') := by simpa using h.b0_zpow_a' 1
    calc (b * b') * (a * a') * (b * b') = ((b * b') * a) * a' * (b * b') := by simp only [mul_assoc]
      _ = a⁻¹ * ((b * b') * a') * (b * b') := by rw [e1]; simp only [mul_assoc]
      _ = a⁻¹ * (a'⁻¹ * (b * b')) * (b * b') := by rw [e2]
      _ = a⁻¹ * a'⁻¹ * ((b * b') * (b * b')) := by simp only [mul_assoc]
      _ = (a * a')⁻¹ := by
        rw [h.b0_sq, mul_one, mul_inv_rev]
        exact h.commute_a_a'.inv_inv.eq
  have hlast : b * b' * t = t * (b * b') := h.t_b0.symm
  calc (b * b' * t) * (a * a') * (b * b' * t)
      = (b * b') * t * (a * a') * (t * (b * b')) := by rw [← hlast]
    _ = (b * b') * (t * (a * a') * t) * (b * b') := by simp only [mul_assoc]
    _ = (a * a')⁻¹ := by rw [h1]; exact h2

theorem t_dl2 (h : Rel a b a' b' t M) : t * (a * a') * t⁻¹ = a * a' := by
  have h0 : t * a' * t = a := by rw [h.ta', mul_assoc, h.t_sq, mul_one]
  rw [h.t_inv]
  calc t * (a * a') * t = (t * a * t) * (t * a' * t) := by
        calc t * (a * a') * t = t * a * (t * t) * a' * t := by
              rw [h.t_sq]; simp only [mul_assoc, mul_one]
          _ = (t * a * t) * (t * a' * t) := by simp only [mul_assoc]
    _ = a * a' := by rw [h.tat, h0, ← h.c_aa]

theorem s2_not_mem_dl2 (h : Rel a b a' b' t M) : b * b' * t ∉ zpowers (a * a') := by
  intro hs
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hs
  rw [h.dl2_zpow] at hk
  have hc : Commute a (b * b' * t) := by rw [← hk]; exact h.commute_a_A k k
  have e : (b * b' * t) * a = a'⁻¹ * (b * b' * t) := by
    have e2 : (b * b') * a' = a'⁻¹ * (b * b') := by simpa using h.b0_zpow_a' 1
    calc (b * b' * t) * a = (b * b') * (t * a) := by rw [mul_assoc]
      _ = (b * b') * (a' * t) := by rw [h.ta]
      _ = ((b * b') * a') * t := (mul_assoc _ _ _).symm
      _ = a'⁻¹ * (b * b' * t) := by rw [e2]; simp only [mul_assoc]
  have h1 : a * (b * b' * t) = a'⁻¹ * (b * b' * t) := by rw [hc.eq, e]
  exact h.a_ne_a'_inv (mul_right_cancel h1)

theorem s2_dl1 (h : Rel a b a' b' t M) : (b * b' * t) * (a * a'⁻¹) * (b * b' * t)⁻¹ = a * a'⁻¹ := by
  rw [h.s2_inv]
  have e1 : (b * b') * a = a⁻¹ * (b * b') := by simpa using h.b0_zpow_a 1
  have e2 : (b * b') * a'⁻¹ = a' * (b * b') := by simpa using h.b0_zpow_a' (-1)
  have h1 : t * (a * a'⁻¹) * t = a' * a⁻¹ := by
    have := h.t_dl1
    rw [h.t_inv, mul_inv_rev, inv_inv] at this
    exact this
  have hlast : b * b' * t = t * (b * b') := h.t_b0.symm
  calc (b * b' * t) * (a * a'⁻¹) * (b * b' * t)
      = (b * b') * t * (a * a'⁻¹) * (t * (b * b')) := by rw [← hlast]
    _ = (b * b') * (t * (a * a'⁻¹) * t) * (b * b') := by simp only [mul_assoc]
    _ = (b * b') * (a' * a⁻¹) * (b * b') := by rw [h1]
    _ = ((b * b') * a') * a⁻¹ * (b * b') := by simp only [mul_assoc]
    _ = a'⁻¹ * (b * b') * a⁻¹ * (b * b') := by rw [show (b * b') * a' = a'⁻¹ * (b * b') by simpa using h.b0_zpow_a' 1]
    _ = a'⁻¹ * ((b * b') * a⁻¹) * (b * b') := by simp only [mul_assoc]
    _ = a'⁻¹ * (a * (b * b')) * (b * b') := by rw [show (b * b') * a⁻¹ = a * (b * b') by simpa using h.b0_zpow_a (-1)]
    _ = a'⁻¹ * a * ((b * b') * (b * b')) := by simp only [mul_assoc]
    _ = a * a'⁻¹ := by rw [h.b0_sq, mul_one]; exact (h.commute_a_a'.inv_right.eq).symm

theorem t_s2 (h : Rel a b a' b' t M) : t * (b * b' * t) * t⁻¹ = b * b' * t := by
  rw [h.t_inv]
  calc t * (b * b' * t) * t = (t * (b * b')) * (t * t) := by simp only [mul_assoc]
    _ = b * b' * t := by rw [h.t_sq, mul_one, h.t_b0]

theorem dl1_M_sq (h : Rel a b a' b' t M) : (a * a'⁻¹) ^ M * (a * a'⁻¹) ^ M = 1 := by
  have := pow_orderOf_eq_one (a * a'⁻¹)
  rw [h.orderOf_dl1, two_mul, pow_add] at this
  exact this

theorem dl2_M (h : Rel a b a' b' t M) : (a * a') ^ M = (a * a'⁻¹) ^ M * a ^ (2 * M) := by
  rw [Commute.mul_pow h.commute_a_a', Commute.mul_pow (h.commute_a_a'.inv_right), inv_pow, ← h.z_eq,
    two_mul, pow_add, mul_assoc, inv_mul_cancel_left]

theorem t_not_comm_a (h : Rel a b a' b' t M) : ¬ Commute a t := by
  intro hc
  have h1 : a' * t = a * t := by rw [← h.ta]; exact hc.eq.symm
  exact h.a_ne_a' (mul_right_cancel h1).symm

theorem b0_not_comm_a (h : Rel a b a' b' t M) : ¬ Commute a (b * b') := by
  intro hc
  have e1 : (b * b') * a = a⁻¹ * (b * b') := by simpa using h.b0_zpow_a 1
  have h1 : a * (b * b') = a⁻¹ * (b * b') := by rw [hc.eq, e1]
  have h2 : a = a⁻¹ := mul_right_cancel h1
  have h3 : a ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [h2]; exact inv_mul_cancel a
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [h.orderOf_a] at h4
  have h5 := Nat.le_of_dvd (by norm_num) h4
  have := h.one_le
  omega

theorem s2_not_comm_a (h : Rel a b a' b' t M) : ¬ Commute a (b * b' * t) := by
  intro hc
  have e2 : (b * b') * a' = a'⁻¹ * (b * b') := by simpa using h.b0_zpow_a' 1
  have e : (b * b' * t) * a = a'⁻¹ * (b * b' * t) := by
    calc (b * b' * t) * a = (b * b') * (t * a) := by rw [mul_assoc]
      _ = (b * b') * (a' * t) := by rw [h.ta]
      _ = ((b * b') * a') * t := (mul_assoc _ _ _).symm
      _ = a'⁻¹ * (b * b' * t) := by rw [e2]; simp only [mul_assoc]
  have h1 : a * (b * b' * t) = a'⁻¹ * (b * b' * t) := by rw [hc.eq, e]
  exact h.a_ne_a'_inv (mul_right_cancel h1)

theorem dl1_M_ne_one (h : Rel a b a' b' t M) : (a * a'⁻¹) ^ M ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by have := h.one_le; omega) (by rw [h.orderOf_dl1]; have := h.one_le; omega)

theorem dl2_M_ne_one (h : Rel a b a' b' t M) : (a * a') ^ M ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by have := h.one_le; omega) (by rw [h.orderOf_dl2]; have := h.one_le; omega)

theorem dl1_M_ne_z (h : Rel a b a' b' t M) : (a * a'⁻¹) ^ M ≠ a ^ (2 * M) := by
  intro e
  apply h.dl2_M_ne_one
  rw [h.dl2_M, e, h.aN_sq]

end Rel

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
