module

import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.OddStandard.ONan76Cent

public section

namespace CFSG.OddStandard.ONan76

section Coord

variable {n : ℕ}

theorem odd_add_self_ne_zero (hn : 2 ≤ n) (m : ZMod (2 ^ n)) : 2 * m + 1 + (2 * m + 1) ≠ 0 := by
  intro h
  have h4 : (2 : ZMod (2 ^ n)) ^ (n - 2) * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ n)) = 2 ^ 2 by norm_num, ← pow_add, show n - 2 + 2 = n by omega]
    exact_mod_cast ZMod.natCast_self (2 ^ n)
  have e : (2 : ZMod (2 ^ n)) ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  apply two_pow_pred_ne_zero (n := n) (by omega)
  calc (2 : ZMod (2 ^ n)) ^ (n - 1)
      = 2 ^ (n - 2) * (2 * m + 1 + (2 * m + 1)) - 2 ^ (n - 2) * 4 * m := by rw [e]; ring
    _ = 0 := by rw [h, h4]; ring

theorem fix_s_t {i : ℕ} (hi : i < 4) {a : ZMod (2 ^ n)}
    (h : act i 1 ((a, 0, a) : Vec n) = (a, 0, a)) : a + a = 0 := by
  interval_cases i <;>
    simp only [act_01, act_11, act_21, act_31, actS, actT, Prod.mk.injEq] at h <;> grind

theorem actS'_fix_s2 (hn : 1 ≤ n) {r : Vec n} (h2 : r + r = 0) (hf : act 2 0 r = r) :
    actS' r = r ∨
      actS' r = r + ((2 : ZMod (2 ^ n)) ^ (n - 1), 0, (2 : ZMod (2 ^ n)) ^ (n - 1)) := by
  obtain ⟨ha, hb, hc⟩ := two_mul_eq_zero_vec hn r h2
  obtain ⟨a, b, c⟩ := r
  simp only at ha hb hc
  have hεε := two_pow_pred_add_self hn (n := n)
  have hε0 := two_pow_pred_ne_zero hn (n := n)
  simp only [act_20, actS, Prod.mk.injEq] at hf
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp only [actS', Prod.mk.injEq, Prod.mk_add_mk] <;> grind

end Coord

namespace AlperinFrame

variable {G : Type*} [Group G] {n : ℕ} {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

theorem vec_s_mul_vec_s (p r : Vec n) (i k : ℕ) :
    vec v₁ v₂ v₃ p * s ^ i * (vec v₁ v₂ v₃ r * s ^ k) =
      vec v₁ v₂ v₃ (p + actS'^[i] r) * s ^ (i + k) := by
  rw [hF.vec_add, pow_add]
  calc vec v₁ v₂ v₃ p * s ^ i * (vec v₁ v₂ v₃ r * s ^ k)
      = vec v₁ v₂ v₃ p * (s ^ i * vec v₁ v₂ v₃ r) * s ^ k := by group
    _ = _ := by rw [hF.s_pow_mul_vec]; group

theorem conj_vec_s (p r : Vec n) (i : ℕ) :
    vec v₁ v₂ v₃ p * s ^ i * (vec v₁ v₂ v₃ r * s ^ 2) * (vec v₁ v₂ v₃ p * s ^ i)⁻¹ =
      vec v₁ v₂ v₃ (p + actS'^[i] r + actS'^[2] (-p)) * s ^ 2 := by
  rw [hF.vec_s_mul_vec_s, mul_inv_rev, ← hF.vec_neg]
  have e : s ^ (i + 2) * (s ^ i)⁻¹ = s ^ 2 := by rw [add_comm, pow_add, mul_inv_cancel_right]
  calc vec v₁ v₂ v₃ (p + actS'^[i] r) * s ^ (i + 2) * ((s ^ i)⁻¹ * vec v₁ v₂ v₃ (-p))
      = vec v₁ v₂ v₃ (p + actS'^[i] r) * (s ^ (i + 2) * (s ^ i)⁻¹) * vec v₁ v₂ v₃ (-p) := by
        group
    _ = vec v₁ v₂ v₃ (p + actS'^[i] r) * (s ^ 2 * vec v₁ v₂ v₃ (-p)) := by rw [e, mul_assoc]
    _ = _ := by rw [hF.s_pow_mul_vec, ← mul_assoc, ← hF.vec_add]

theorem vec_one_zero_one (hn : 1 ≤ n) : vec v₁ v₂ v₃ ((1, 0, 1) : Vec n) = v₁ * v₃ := by
  rw [show ((1, 0, 1) : Vec n) = (1, 0, 0) + (0, 0, 1) by simp, hF.vec_add, hF.vec_e1 hn,
    hF.vec_e3 hn]

theorem conj_vec_s_vec (q p : Vec n) (i : ℕ) :
    vec v₁ v₂ v₃ q * s ^ i * vec v₁ v₂ v₃ p * (vec v₁ v₂ v₃ q * s ^ i)⁻¹ =
      vec v₁ v₂ v₃ (actS'^[i] p) := by
  rw [mul_inv_rev, mul_assoc (vec v₁ v₂ v₃ q), hF.s_pow_mul_vec]
  calc vec v₁ v₂ v₃ q * (vec v₁ v₂ v₃ (actS'^[i] p) * s ^ i) * ((s ^ i)⁻¹ * (vec v₁ v₂ v₃ q)⁻¹)
      = vec v₁ v₂ v₃ q * vec v₁ v₂ v₃ (actS'^[i] p) * (vec v₁ v₂ v₃ q)⁻¹ := by group
    _ = _ := by rw [hF.vec_comm, mul_inv_cancel_right]

end AlperinFrame

end CFSG.OddStandard.ONan76
