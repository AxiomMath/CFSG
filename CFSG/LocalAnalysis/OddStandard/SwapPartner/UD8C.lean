module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8B
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] {z g x : G}

namespace D8Rel

lemma u_comm_AA (h : D8Rel z g x) (i j : ℤ) :
    ⁅(z * g) ^ i, (z * g) ^ j⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm, u_zpow_mul h, u_zpow_mul h]
  congr 1; ring

lemma u_comm_AB (h : D8Rel z g x) (i j : ℤ) :
    ⁅(z * g) ^ i, (z * g) ^ j * g⁆ = x ^ i := by
  have hb : ((z * g) ^ j * g)⁻¹ = (z * g) ^ j * g := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.g_sq, ← zpow_neg,
      u_B_mul_zpow h (-j), neg_neg]
  rw [commutatorElement_def, hb, ← zpow_neg]
  rw [show (z*g)^i * ((z*g)^j * g) * (z*g)^(-i) * ((z*g)^j * g)
        = (z*g)^i * (z*g)^j * (g * (z*g)^(-i)) * (z*g)^j * g from by group]
  rw [u_B_mul_zpow h (-i), neg_neg]
  rw [show (z*g)^i * (z*g)^j * ((z*g)^i * g) * (z*g)^j * g
        = (z*g)^i * (z*g)^j * (z*g)^i * (g * (z*g)^j) * g from by group]
  rw [u_B_mul_zpow h j]
  rw [show (z*g)^i * (z*g)^j * (z*g)^i * ((z*g)^(-j) * g) * g
        = ((z*g)^i * (z*g)^j * (z*g)^i * (z*g)^(-j)) * (g * g) from by group]
  rw [h.g_sq, mul_one, u_zpow_mul h, u_zpow_mul h, u_zpow_mul h,
    show i + j + i + -j = 2 * i from by ring, zpow_mul, u_A_sq_zpow h]

lemma u_comm_BA (h : D8Rel z g x) (i j : ℤ) :
    ⁅(z * g) ^ i * g, (z * g) ^ j⁆ = x ^ (-j) := by
  have ha : ((z * g) ^ i * g)⁻¹ = (z * g) ^ i * g := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.g_sq, ← zpow_neg,
      u_B_mul_zpow h (-i), neg_neg]
  rw [commutatorElement_def, ha, ← zpow_neg]
  rw [show ((z*g)^i * g) * (z*g)^j * ((z*g)^i * g) * (z*g)^(-j)
        = (z*g)^i * (g * (z*g)^j) * ((z*g)^i * g) * (z*g)^(-j) from by group]
  rw [u_B_mul_zpow h j]
  rw [show (z*g)^i * ((z*g)^(-j) * g) * ((z*g)^i * g) * (z*g)^(-j)
        = (z*g)^i * (z*g)^(-j) * (g * (z*g)^i) * g * (z*g)^(-j) from by group]
  rw [u_B_mul_zpow h i]
  rw [show (z*g)^i * (z*g)^(-j) * ((z*g)^(-i) * g) * g * (z*g)^(-j)
        = ((z*g)^i * (z*g)^(-j) * (z*g)^(-i)) * (g * g) * (z*g)^(-j) from by group]
  rw [h.g_sq, mul_one, u_zpow_mul h, u_zpow_mul h, u_zpow_mul h,
    show i + -j + -i + -j = 2 * (-j) from by ring, zpow_mul, u_A_sq_zpow h]

lemma u_comm_BB (h : D8Rel z g x) (i j : ℤ) :
    ⁅(z * g) ^ i * g, (z * g) ^ j * g⁆ = x ^ (i - j) := by
  have ha : ((z * g) ^ i * g)⁻¹ = (z * g) ^ i * g := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.g_sq, ← zpow_neg,
      u_B_mul_zpow h (-i), neg_neg]
  have hb : ((z * g) ^ j * g)⁻¹ = (z * g) ^ j * g := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.g_sq, ← zpow_neg,
      u_B_mul_zpow h (-j), neg_neg]
  rw [commutatorElement_def, ha, hb]
  rw [show ((z*g)^i * g) * ((z*g)^j * g) * ((z*g)^i * g) * ((z*g)^j * g)
        = (z*g)^i * (g * (z*g)^j) * g * (z*g)^i * (g * (z*g)^j) * g from by group]
  rw [u_B_mul_zpow h j]
  rw [show (z*g)^i * ((z*g)^(-j) * g) * g * (z*g)^i * ((z*g)^(-j) * g) * g
        = ((z*g)^i * (z*g)^(-j)) * (g * g) * ((z*g)^i * (z*g)^(-j)) * (g * g)
          from by group]
  rw [h.g_sq]
  simp only [mul_one, one_mul]
  rw [u_zpow_mul h, u_zpow_mul h,
    show i + -j + (i + -j) = 2 * (i - j) from by ring, zpow_mul, u_A_sq_zpow h]

theorem commutator_mem (h : D8Rel z g x) {a b : G} (ha : a ∈ closure ({z, g} : Set G))
    (hb : b ∈ closure ({z, g} : Set G)) : ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = x := by
  rcases (u_form h a).mp ha with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases (u_form h b).mp hb with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left; exact u_comm_AA h i j
  · rw [u_comm_AB h i j]; exact u_x_zpow_cases h i
  · rw [u_comm_BA h i j]; exact u_x_zpow_cases h (-j)
  · rw [u_comm_BB h i j]; exact u_x_zpow_cases h (i - j)

theorem commutator_z_g (h : D8Rel z g x) : ⁅z, g⁆ = x := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right h.z_sq,
    inv_eq_of_mul_eq_one_right h.g_sq]
  exact h.x_eq

theorem sq_eq_one_iff (h : D8Rel z g x) {q : G} (hq : q ∈ closure ({z, g} : Set G)) :
    q * q = 1 ↔ q = 1 ∨ q = z ∨ q = g ∨ q = z * g * z ∨ q = g * z * g ∨ q = x := by
  rw [mem_closure_iff h q] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · rw [h.z_sq]; simp
  · rw [h.g_sq]; simp
  · constructor
    · intro h1
      rw [u_AA h] at h1
      exact absurd h1 h.x_ne
    · rintro (h1 | h1 | h1 | h1 | h1 | h1)
      · rw [h1, one_mul]
      · rw [h1, h.z_sq]
      · rw [h1, h.g_sq]
      · rw [h1]; exact u_zgz_sq h
      · rw [h1]; exact u_gzg_sq h
      · rw [h1]; exact h.x_sq
  · constructor
    · intro h1
      rw [u_gz_sq h] at h1
      exact absurd h1 h.x_ne
    · rintro (h1 | h1 | h1 | h1 | h1 | h1)
      · rw [h1, one_mul]
      · rw [h1, h.z_sq]
      · rw [h1, h.g_sq]
      · rw [h1]; exact u_zgz_sq h
      · rw [h1]; exact u_gzg_sq h
      · rw [h1]; exact h.x_sq
  · constructor
    · intro _
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · intro _; exact u_zgz_sq h
  · constructor
    · intro _
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · intro _; exact u_gzg_sq h
  · constructor
    · intro _
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · intro _; exact h.x_sq

end D8Rel

end CFSG.OddStandard.AltStdSec.SwapPartner
