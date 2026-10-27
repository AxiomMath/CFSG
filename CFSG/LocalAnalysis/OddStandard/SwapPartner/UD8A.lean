module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] {z g x : G}

structure D8Rel (z g x : G) : Prop where
  z_sq : z * z = 1
  g_sq : g * g = 1
  x_eq : z * g * z * g = x
  x_ne : x ≠ 1
  x_sq : x * x = 1

namespace D8Rel

theorem z_mem (z g : G) : z ∈ closure ({z, g} : Set G) :=
  subset_closure (Set.mem_insert z _)

theorem g_mem (z g : G) : g ∈ closure ({z, g} : Set G) :=
  subset_closure (Set.mem_insert_of_mem z (Set.mem_singleton g))

section Helpers

variable (h : D8Rel z g x)

include h

lemma u_gzgz : g * z * g * z = x := by
  have hgz : g * z = (z * g)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.z_sq, inv_eq_of_mul_eq_one_right h.g_sq]
  have h2 : (g * z) * (g * z) = ((z * g) * (z * g))⁻¹ := by
    rw [mul_inv_rev, hgz]
  rw [mul_assoc (g * z) g z, h2, show (z * g) * (z * g) = x from by
    rw [← mul_assoc]; exact h.x_eq, inv_eq_of_mul_eq_one_right h.x_sq]

lemma u_A_sq_nat : (z * g) ^ 2 = x := by
  rw [pow_two, ← mul_assoc]
  exact h.x_eq

lemma u_A_sq_zpow : (z * g) ^ (2 : ℤ) = x := by
  show (z * g) ^ ((2 : ℕ) : ℤ) = x
  rw [zpow_natCast, u_A_sq_nat h]

lemma u_A_four_nat : (z * g) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, u_A_sq_nat h, pow_two, h.x_sq]

lemma u_A_four_zpow : (z * g) ^ (4 : ℤ) = 1 := by
  show (z * g) ^ ((4 : ℕ) : ℤ) = 1
  rw [zpow_natCast, u_A_four_nat h]

lemma u_A_cube_zpow : (z * g) ^ (3 : ℤ) = g * z := by
  have h1 : (z * g) ^ (3 : ℤ) * (z * g) = 1 := by
    rw [← zpow_add_one (z * g) 3, show (3 : ℤ) + 1 = 4 from rfl, u_A_four_zpow h]
  rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev,
    inv_eq_of_mul_eq_one_right h.z_sq, inv_eq_of_mul_eq_one_right h.g_sq]

lemma u_AA : (z * g) * (z * g) = x := by
  rw [← mul_assoc]
  exact h.x_eq

lemma u_gz_sq : (g * z) * (g * z) = x := by
  rw [← mul_assoc]
  exact u_gzgz h

lemma u_zpow_mul (m n : ℤ) :
    (z * g) ^ m * (z * g) ^ n = (z * g) ^ (m + n) :=
  (zpow_add (z * g) m n).symm

lemma u_orderOf_A : orderOf (z * g) = 4 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (n := 4) (by norm_num) (u_A_four_nat h) ?_
  intro p hp hpdvd
  have hp2 : p = 2 := by
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 2) (by simpa using hpdvd)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hge : 2 ≤ p := hp.two_le
    omega
  subst hp2
  rw [show 4 / 2 = 2 from rfl, u_A_sq_nat h]
  exact h.x_ne

lemma u_zpow_mod (k : ℤ) : (z * g) ^ k = (z * g) ^ (k % 4) := by
  rw [← zpow_mod_orderOf (z * g) k, u_orderOf_A h]
  norm_num

lemma u_BAB : g * (z * g) * g = (z * g)⁻¹ := by
  rw [← mul_assoc g z g, mul_assoc (g * z) g g, h.g_sq, mul_one, mul_inv_rev,
    inv_eq_of_mul_eq_one_right h.z_sq, inv_eq_of_mul_eq_one_right h.g_sq]

lemma u_B_mul_zpow (i : ℤ) : g * (z * g) ^ i = (z * g) ^ (-i) * g := by
  have hc : MulAut.conj g ((z * g) ^ i) = ((z * g) ^ i)⁻¹ := by
    calc MulAut.conj g ((z * g) ^ i) = (MulAut.conj g (z * g)) ^ i :=
          map_zpow (MulAut.conj g) (z * g) i
      _ = ((z * g)⁻¹) ^ i := by
            rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right h.g_sq, u_BAB h]
      _ = ((z * g) ^ i)⁻¹ := inv_zpow _ _
  have h2 : g * (z * g) ^ i = ((z * g) ^ i)⁻¹ * g := by
    have := congrArg (· * g) hc
    simpa [MulAut.conj_apply, inv_eq_of_mul_eq_one_right h.g_sq, mul_assoc, h.g_sq]
      using this
  rw [h2, ← zpow_neg]

lemma u_B_not_mem : g ∉ zpowers (z * g) := by
  intro hg
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg
  have hcomm : Commute ((z * g) ^ k) (z * g) := Commute.zpow_self (z * g) k
  rw [hk] at hcomm
  have hcm : g * (z * g) = (z * g) * g := hcomm.eq
  have hAeq : (z * g) = (z * g)⁻¹ := by
    calc (z * g) = (z * g) * g * g := by rw [mul_assoc (z * g) g g, h.g_sq, mul_one]
      _ = g * (z * g) * g := by rw [← hcm]
      _ = (z * g)⁻¹ := u_BAB h
  have h2 : (z * g) * (z * g) = 1 := by
    nth_rewrite 2 [hAeq]
    exact mul_inv_cancel (z * g)
  rw [u_AA h] at h2
  exact h.x_ne h2

lemma u_form_mul {a b : G}
    (ha : (∃ i : ℤ, a = (z * g) ^ i) ∨ (∃ i : ℤ, a = (z * g) ^ i * g))
    (hb : (∃ i : ℤ, b = (z * g) ^ i) ∨ (∃ i : ℤ, b = (z * g) ^ i * g)) :
    (∃ i : ℤ, a * b = (z * g) ^ i) ∨ (∃ i : ℤ, a * b = (z * g) ^ i * g) := by
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hb with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left; exact ⟨i + j, by rw [u_zpow_mul h]⟩
  · right; refine ⟨i + j, ?_⟩
    rw [← mul_assoc, u_zpow_mul h]
  · right; refine ⟨i - j, ?_⟩
    calc (z * g) ^ i * g * (z * g) ^ j
        = (z * g) ^ i * (g * (z * g) ^ j) := by group
      _ = (z * g) ^ i * ((z * g) ^ (-j) * g) := by rw [u_B_mul_zpow h j]
      _ = ((z * g) ^ i * (z * g) ^ (-j)) * g := by group
      _ = (z * g) ^ (i - j) * g := by
            rw [u_zpow_mul h, show i + -j = i - j from by ring]
  · left; refine ⟨i - j, ?_⟩
    calc (z * g) ^ i * g * ((z * g) ^ j * g)
        = (z * g) ^ i * (g * (z * g) ^ j) * g := by group
      _ = (z * g) ^ i * ((z * g) ^ (-j) * g) * g := by rw [u_B_mul_zpow h j]
      _ = ((z * g) ^ i * (z * g) ^ (-j)) * (g * g) := by group
      _ = (z * g) ^ (i - j) := by
            rw [u_zpow_mul h, h.g_sq, mul_one, show i + -j = i - j from by ring]

lemma u_form_inv {a : G}
    (ha : (∃ i : ℤ, a = (z * g) ^ i) ∨ (∃ i : ℤ, a = (z * g) ^ i * g)) :
    (∃ i : ℤ, a⁻¹ = (z * g) ^ i) ∨ (∃ i : ℤ, a⁻¹ = (z * g) ^ i * g) := by
  rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · left; exact ⟨-i, by rw [← zpow_neg]⟩
  · right; refine ⟨i, ?_⟩
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.g_sq, ← zpow_neg,
      u_B_mul_zpow h (-i), neg_neg]

lemma u_form (q : G) :
    q ∈ closure ({z, g} : Set G) ↔
      (∃ i : ℤ, q = (z * g) ^ i) ∨ (∃ i : ℤ, q = (z * g) ^ i * g) := by
  constructor
  · intro hq
    refine Subgroup.closure_induction (p := fun q _ =>
      (∃ i : ℤ, q = (z * g) ^ i) ∨ (∃ i : ℤ, q = (z * g) ^ i * g)) ?_ ?_ ?_ ?_ hq
    · intro y hy
      rcases hy with rfl | rfl
      · right; refine ⟨1, ?_⟩
        rw [zpow_one, mul_assoc, h.g_sq, mul_one]
      · right; exact ⟨0, by simp⟩
    · left; exact ⟨0, by simp⟩
    · intro a b _ _ ha hb; exact u_form_mul h ha hb
    · intro a _ ha; exact u_form_inv h ha
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Subgroup.zpow_mem _ (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) i
    · exact mul_mem
        (Subgroup.zpow_mem _ (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) i)
        (subset_closure (by simp))

lemma u_zpow_cases (i : ℤ) :
    (z * g) ^ i = 1 ∨ (z * g) ^ i = z * g ∨ (z * g) ^ i = x ∨
      (z * g) ^ i = g * z := by
  rw [u_zpow_mod h i]
  set k : ℤ := i % 4 with hk
  have hk0 : 0 ≤ k := by rw [hk]; exact Int.emod_nonneg i (by norm_num)
  have hk4 : k < 4 := by rw [hk]; exact Int.emod_lt_of_pos i (by norm_num)
  interval_cases k <;> simp [u_A_sq_zpow h, u_A_cube_zpow h]

end Helpers

end D8Rel

end CFSG.OddStandard.AltStdSec.SwapPartner
