module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveQForm
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveBasic

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G] {P S : Subgroup G} {s x : G} {a : ℕ}

theorem QData.exists_mul_self_eq_mul_pow (h : QData P S s x a) {z : G}
    (hz : z ∈ QData.group P S x) : ∃ c ∈ P, ∃ m : ℕ, z * z = c * s ^ m := by
  obtain ⟨l, hl, -, -⟩ := h.exists_lambda
  obtain ⟨p, hp, j, e, he, rfl⟩ := (h.mem_group_iff z).1 hz
  interval_cases e
  · exact ⟨1, P.one_mem, 2 * j, by rw [pow_zero, mul_one, h.sq_PS hp, one_mul]⟩
  · exact ⟨p * (x * p * x⁻¹), P.mul_mem hp (h.x_normalizes_P p hp), j + l * j,
      by rw [pow_one, h.sq_outer hl hp]⟩

theorem QData.pow_four_mem_zpowers (h : QData P S s x a) {z : G}
    (hz : z ∈ QData.group P S x) : z ^ 4 ∈ zpowers s := by
  obtain ⟨c, hc, m, hm⟩ := h.exists_mul_self_eq_mul_pow hz
  rw [show z ^ 4 = z * z * (z * z) by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq], hm,
    h.sq_PS hc m]
  exact npow_mem_zpowers s _

theorem QData.eq_of_mem_zpowers_of_mul_self_eq_one (h : QData P S s x a) {u : G}
    (hu : u ∈ zpowers s) (hu2 : u * u = 1) (hu1 : u ≠ 1) : u = s ^ 2 ^ (a - 1) :=
  eq_pow_of_mem_zpowers_of_orderOf_eq_two h.orderOf_s hu
    (orderOf_eq_prime (by rw [sq]; exact hu2) hu1)

theorem QData.conj_s_eq_of_two (h : QData P S s x a) (hnot : ¬ x * s * x⁻¹ = s⁻¹)
    (ha : a = 2) : x * s * x⁻¹ = s := by
  obtain ⟨l, hl, ⟨k, rfl⟩, -⟩ := h.exists_lambda
  have hs4 : orderOf s = 4 := by rw [h.orderOf_s, ha]; norm_num
  have hs4' : s ^ 4 = 1 := by rw [← hs4]; exact pow_orderOf_eq_one s
  have hmod : s ^ (2 * k + 1) = s ^ ((2 * k + 1) % 4) := by rw [← hs4, pow_mod_orderOf]
  rcases (show (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 by omega) with h1 | h3
  · rw [hl, hmod, h1, pow_one]
  · refine absurd ?_ hnot
    rw [hl, hmod, h3, eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hs4'

theorem QData.commute_s_of_conj_s_eq (h : QData P S s x a) (hxs : x * s * x⁻¹ = s) {g : G}
    (hg : g ∈ QData.group P S x) : s * g = g * s := by
  obtain ⟨p, hp, j, e, -, rfl⟩ := (h.mem_group_iff g).1 hg
  have hx : Commute s x := by
    rw [mul_inv_eq_iff_eq_mul] at hxs
    exact hxs.symm
  have hps : Commute s p := (h.P_comm_s p hp).symm
  exact ((hps.mul_right (Commute.self_pow s j)).mul_right (hx.pow_right e)).eq

theorem QData.mul_self_mem_zpowers_of_commute (h : QData P S s x a) {z : G}
    (hz : z ∈ QData.group P S x) (hzP : ∀ p ∈ P, z * p = p * z) : z * z ∈ zpowers s := by
  obtain ⟨p, hp, j, e, he, rfl⟩ := (h.mem_group_iff z).1 hz
  interval_cases e
  · rw [pow_zero, mul_one, h.sq_PS hp]
    exact npow_mem_zpowers s _
  · exfalso
    obtain ⟨p₁, hp₁, hne⟩ := h.x_acts_nontrivially
    apply hne
    have hsj : s ^ j ∈ S := by rw [h.S_eq]; exact npow_mem_zpowers s j
    have hc : Commute (p * s ^ j) p₁ :=
      Commute.mul_left (h.P_comm p hp p₁ hp₁) (h.P_comm_S p₁ hp₁ (s ^ j) hsj).symm
    have key : (p * s ^ j) * (x * p₁) = (p * s ^ j) * (p₁ * x) := by
      calc (p * s ^ j) * (x * p₁) = p * s ^ j * x ^ 1 * p₁ := by rw [pow_one, ← mul_assoc]
        _ = p₁ * (p * s ^ j * x ^ 1) := hzP p₁ hp₁
        _ = (p * s ^ j) * (p₁ * x) := by rw [pow_one, ← mul_assoc, ← hc.eq, mul_assoc]
    rw [mul_left_cancel key, mul_inv_cancel_right]

theorem QData.normalizer_fixes_t (h : QData P S s x a) (hnot : ¬ x * s * x⁻¹ = s⁻¹) {t : G}
    (ht : t = s ^ 2 ^ (a - 1)) :
    ∀ n ∈ normalizer ((QData.group P S x : Subgroup G) : Set G), n * t * n⁻¹ = t := by
  intro n hn
  have hsQ : s ∈ QData.group P S x :=
    mem_sup_left (mem_sup_right (by rw [h.S_eq]; exact mem_zpowers s))
  have hqQ : n * s * n⁻¹ ∈ QData.group P S x := (mem_normalizer_iff.1 hn s).1 hsQ
  have ha1 : 1 ≤ a := le_trans (by norm_num) h.two_le
  have hpow : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel ha1]
  have ht1 : t ≠ 1 := by
    rw [ht]
    exact pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [h.orderOf_s]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have htt : t * t = 1 := by
    rw [ht, ← pow_add, hpow, ← h.orderOf_s, pow_orderOf_eq_one]
  have hu1 : n * t * n⁻¹ ≠ 1 := fun h1 => ht1 (conj_eq_one_iff.1 h1)
  have hu2 : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    rw [conj_mul, htt, mul_one, mul_inv_cancel]
  have hconj : n * t * n⁻¹ = (n * s * n⁻¹) ^ 2 ^ (a - 1) := by rw [ht, conj_pow]
  suffices hmem : n * t * n⁻¹ ∈ zpowers s from
    (h.eq_of_mem_zpowers_of_mul_self_eq_one hmem hu2 hu1).trans ht.symm
  rcases (show a = 2 ∨ 3 ≤ a by have := h.two_le; omega) with ha | ha
  · have hxs := h.conj_s_eq_of_two hnot ha
    subst ha
    rw [hconj, show (2 : ℕ) ^ (2 - 1) = 2 by norm_num, sq]
    refine h.mul_self_mem_zpowers_of_commute hqQ fun p hp => ?_
    have hpQ : p ∈ QData.group P S x := mem_sup_left (mem_sup_left hp)
    have hc := h.commute_s_of_conj_s_eq hxs ((mem_normalizer_iff''.1 hn p).1 hpQ)
    calc n * s * n⁻¹ * p = n * (s * (n⁻¹ * p * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * p * n) * s) * n⁻¹ := by rw [hc]
      _ = p * (n * s * n⁻¹) := by group
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
    have h4 : (n * s * n⁻¹) ^ 2 ^ (b + 3 - 1) = ((n * s * n⁻¹) ^ 2 ^ b) ^ 4 := by
      rw [← pow_mul, show b + 3 - 1 = b + 2 by omega, pow_add]
      norm_num
    rw [hconj, h4]
    exact h.pow_four_mem_zpowers ((QData.group P S x).pow_mem hqQ _)

end CFSG.OddStandard
