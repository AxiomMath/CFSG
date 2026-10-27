module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8A
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] {z g x : G}

namespace D8Rel

section Helpers

variable (h : D8Rel z g x)

include h

lemma u_x_mul_g : x * g = z * g * z := by
  rw [← h.x_eq]
  show (z * g * z * g) * g = z * g * z
  rw [mul_assoc (z * g * z) g g, h.g_sq, mul_one]

lemma u_g_mul_x : g * x = z * g * z := by
  rw [← h.x_eq]
  rw [show g * (z * g * z * g) = (g * z * g * z) * g from by group, u_gzgz h, u_x_mul_g h]

lemma u_x_mul_z : x * z = g * z * g := by
  have hx : x = g * (z * g * z) := by
    rw [← u_g_mul_x h, ← mul_assoc, h.g_sq, one_mul]
  rw [hx, mul_assoc g (z * g * z) z, mul_assoc (z * g) z z, h.z_sq, mul_one,
    ← mul_assoc g z g]

lemma u_z_mul_x : z * x = g * z * g := by
  rw [← h.x_eq]
  rw [show z * (z * g * z * g) = z * z * g * z * g from by group, h.z_sq, one_mul]

lemma u_x_comm_z : x * z = z * x := by
  rw [u_x_mul_z h, u_z_mul_x h]

lemma u_x_comm_g : x * g = g * x := by
  rw [u_x_mul_g h, u_g_mul_x h]

lemma u_zgz_mul_x : (z * g * z) * x = g := by
  rw [← u_g_mul_x h, mul_assoc, h.x_sq, mul_one]

lemma u_gzg_mul_x : (g * z * g) * x = z := by
  rw [← u_z_mul_x h, mul_assoc, h.x_sq, mul_one]

lemma u_zg_mul_gzg : (z * g) * (g * z * g) = g := by
  rw [← u_z_mul_x h, show (z * g) * (z * x) = (z * g * z) * x from by group,
    ← u_g_mul_x h, mul_assoc g x x, h.x_sq, mul_one]

lemma u_g_mul_gzg : g * (g * z * g) = z * g := by
  rw [show g * (g * z * g) = g * g * z * g from by group, h.g_sq, one_mul]

lemma u_g_mul_gz : g * (g * z) = z := by
  rw [← mul_assoc, h.g_sq, one_mul]

lemma u_inv_gz : (g * z)⁻¹ = z * g := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.z_sq, inv_eq_of_mul_eq_one_right h.g_sq]

lemma u_zgz_sq : (z * g * z) * (z * g * z) = 1 := by
  rw [← u_g_mul_x h, ← mul_assoc (g * x) g x, mul_assoc g x g, u_x_comm_g h,
    ← mul_assoc g g x, h.g_sq, one_mul, h.x_sq]

lemma u_gzg_sq : (g * z * g) * (g * z * g) = 1 := by
  rw [← u_z_mul_x h, ← mul_assoc (z * x) z x, mul_assoc z x z, u_x_comm_z h,
    ← mul_assoc z z x, h.z_sq, one_mul, h.x_sq]

lemma u_zpowB_cases (i : ℤ) :
    (z * g) ^ i * g = g ∨ (z * g) ^ i * g = z ∨
      (z * g) ^ i * g = z * g * z ∨ (z * g) ^ i * g = g * z * g := by
  rcases u_zpow_cases h i with hh | hh | hh | hh <;> rw [hh]
  · left; rw [one_mul]
  · right; left; rw [mul_assoc, h.g_sq, mul_one]
  · right; right; left; rw [u_x_mul_g h]
  · right; right; right; rfl

lemma u_x_zpow_cases (i : ℤ) : x ^ i = 1 ∨ x ^ i = x := by
  have h2 : orderOf x = 2 := by
    refine orderOf_eq_prime (p := 2) ?_ h.x_ne
    rw [pow_two]; exact h.x_sq
  have hmod : x ^ (i % 2) = x ^ i := by
    rw [← zpow_mod_orderOf x i, h2]
    norm_num
  rw [← hmod]
  set k : ℤ := i % 2 with hk
  have hk0 : 0 ≤ k := by rw [hk]; exact Int.emod_nonneg i (by norm_num)
  have hk2 : k < 2 := by rw [hk]; exact Int.emod_lt_of_pos i (by norm_num)
  interval_cases k <;> simp

lemma u_g_ne_one : g ≠ 1 := by
  intro hg
  apply h.x_ne
  rw [← h.x_eq, hg]
  simp [h.z_sq]

lemma u_gx_ne_one : g * x ≠ 1 := by
  intro hgx
  have hxg : x = g := by
    calc x = (g * g) * x := by rw [h.g_sq, one_mul]
      _ = g * (g * x) := by group
      _ = g := by rw [hgx, mul_one]
  have h2 : z * x * z * x = 1 := by
    rw [(u_x_comm_z h).symm, mul_assoc x z z, h.z_sq, mul_one, h.x_sq]
  have h1 : z * x * z * x = x := by
    have hx_eq := h.x_eq
    rw [← hxg] at hx_eq
    exact hx_eq
  rw [h2] at h1
  exact h.x_ne h1.symm

lemma u_g_ne_x : g ≠ x := by
  intro hgx
  apply h.x_ne
  rw [← h.x_eq, hgx, (u_x_comm_z h).symm, mul_assoc x z z, h.z_sq, mul_one, h.x_sq]

lemma u_gx_ne_x : g * x ≠ x := by
  intro hgxx
  have hg1 : g = 1 := by
    have h' := congrArg (· * x) hgxx
    rw [mul_assoc g x x, h.x_sq, mul_one] at h'
    exact h'
  exact u_g_ne_one h hg1

lemma u_gx_ne_g : g * x ≠ g := by
  intro hgxg
  have hx1 : x = 1 := by
    have h' := congrArg (· * g) hgxg
    rw [mul_assoc g x g, u_x_comm_g h, ← mul_assoc g g x, h.g_sq, one_mul] at h'
    exact h'
  exact h.x_ne hx1

end Helpers

theorem x_comm_z (h : D8Rel z g x) : x * z = z * x := by
  rw [u_x_mul_z h, u_z_mul_x h]

theorem x_comm_g (h : D8Rel z g x) : x * g = g * x := by
  rw [u_x_mul_g h, u_g_mul_x h]

theorem mem_closure_iff (h : D8Rel z g x) (q : G) :
    q ∈ closure ({z, g} : Set G) ↔
      q = 1 ∨ q = z ∨ q = g ∨ q = z * g ∨ q = g * z ∨ q = z * g * z ∨ q = g * z * g ∨ q = x := by
  constructor
  · intro hq
    rcases (u_form h q).mp hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases u_zpow_cases h i with hh | hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))
    · rcases u_zpowB_cases h i with hh | hh | hh | hh
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  · intro hq
    rcases hq with e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8
    · rw [e1]; exact one_mem _
    · rw [e2]; exact z_mem z g
    · rw [e3]; exact g_mem z g
    · rw [e4]; exact mul_mem (z_mem z g) (g_mem z g)
    · rw [e5]; exact mul_mem (g_mem z g) (z_mem z g)
    · rw [e6]; exact mul_mem (mul_mem (z_mem z g) (g_mem z g)) (z_mem z g)
    · rw [e7]; exact mul_mem (mul_mem (g_mem z g) (z_mem z g)) (g_mem z g)
    · rw [e8, ← u_A_sq_zpow h]
      exact Subgroup.zpow_mem _ (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) 2

theorem x_comm (h : D8Rel z g x) {q : G} (hq : q ∈ closure ({z, g} : Set G)) :
    q * x = x * q := by
  have hAx : ∀ i : ℤ, (z * g) ^ i * x = x * (z * g) ^ i := by
    intro i
    rw [← u_A_sq_zpow h, u_zpow_mul h, u_zpow_mul h]
    congr 1; ring
  rcases (u_form h q).mp hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hAx i
  · calc (z * g) ^ i * g * x = (z * g) ^ i * (g * x) := by group
      _ = (z * g) ^ i * (x * g) := by rw [u_g_mul_x h, u_x_mul_g h]
      _ = ((z * g) ^ i * x) * g := by group
      _ = (x * (z * g) ^ i) * g := by rw [hAx i]
      _ = x * ((z * g) ^ i * g) := by group

theorem x_mem (h : D8Rel z g x) : x ∈ closure ({z, g} : Set G) := by
  rw [← u_A_sq_zpow h]
  exact Subgroup.zpow_mem _ (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) 2

def u_F (h : D8Rel z g x) (p : Fin 4 × Bool) : closure ({z, g} : Set G) :=
  match p.2 with
  | false => ⟨(z * g) ^ ((p.1 : ℤ)),
      Subgroup.zpow_mem _ (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) _⟩
  | true => ⟨(z * g) ^ ((p.1 : ℤ)) * g,
      mul_mem (Subgroup.zpow_mem _
        (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) _)
        (subset_closure (by simp))⟩

lemma u_F_bijective (h : D8Rel z g x) : Function.Bijective (u_F h) := by
  constructor
  · intro p q hpq
    have hval : (u_F h p : G) = (u_F h q : G) := congrArg Subtype.val hpq
    rcases p with ⟨kp, bp⟩
    rcases q with ⟨kq, bq⟩
    cases bp <;> cases bq
    · simp only [u_F] at hval
      have hk : ((kp : ℤ)) ≡ ((kq : ℤ)) [ZMOD 4] := by
        rw [zpow_eq_zpow_iff_modEq, u_orderOf_A h] at hval
        exact hval
      have hk' : (kp : ℤ) % 4 = (kq : ℤ) % 4 := hk
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast kp.isLt),
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast kq.isLt)] at hk'
      exact Prod.ext (Fin.ext (by exact_mod_cast hk')) rfl
    · simp only [u_F] at hval
      exfalso
      apply u_B_not_mem h
      rw [mem_zpowers_iff]
      refine ⟨(kp : ℤ) - (kq : ℤ), ?_⟩
      have hg : g = (z * g) ^ ((kp : ℤ) - (kq : ℤ)) := by
        calc g = ((z * g) ^ (kq : ℤ))⁻¹ * ((z * g) ^ (kq : ℤ) * g) := by group
          _ = ((z * g) ^ (kq : ℤ))⁻¹ * (z * g) ^ (kp : ℤ) := by rw [← hval]
          _ = (z * g) ^ (-(kq : ℤ)) * (z * g) ^ (kp : ℤ) := by rw [← zpow_neg]
          _ = (z * g) ^ ((kp : ℤ) - (kq : ℤ)) := by
                rw [u_zpow_mul h, show -(kq : ℤ) + (kp : ℤ) = (kp : ℤ) - (kq : ℤ) from by ring]
      exact hg.symm
    · simp only [u_F] at hval
      exfalso
      apply u_B_not_mem h
      rw [mem_zpowers_iff]
      refine ⟨(kq : ℤ) - (kp : ℤ), ?_⟩
      have hg : g = (z * g) ^ ((kq : ℤ) - (kp : ℤ)) := by
        calc g = ((z * g) ^ (kp : ℤ))⁻¹ * ((z * g) ^ (kp : ℤ) * g) := by group
          _ = ((z * g) ^ (kp : ℤ))⁻¹ * (z * g) ^ (kq : ℤ) := by rw [hval]
          _ = (z * g) ^ (-(kp : ℤ)) * (z * g) ^ (kq : ℤ) := by rw [← zpow_neg]
          _ = (z * g) ^ ((kq : ℤ) - (kp : ℤ)) := by
                rw [u_zpow_mul h, show -(kp : ℤ) + (kq : ℤ) = (kq : ℤ) - (kp : ℤ) from by ring]
      exact hg.symm
    · simp only [u_F] at hval
      have hval' : (z * g) ^ (kp : ℤ) = (z * g) ^ (kq : ℤ) := mul_right_cancel hval
      have hk : ((kp : ℤ)) ≡ ((kq : ℤ)) [ZMOD 4] := by
        rw [zpow_eq_zpow_iff_modEq, u_orderOf_A h] at hval'
        exact hval'
      have hk' : (kp : ℤ) % 4 = (kq : ℤ) % 4 := hk
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast kp.isLt),
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast kq.isLt)] at hk'
      exact Prod.ext (Fin.ext (by exact_mod_cast hk')) rfl
  · rintro ⟨q, hq⟩
    rcases (u_form h q).mp hq with ⟨i, hi⟩ | ⟨i, hi⟩
    · have h0 : 0 ≤ i % 4 := Int.emod_nonneg i (by norm_num)
      have h4 : i % 4 < 4 := Int.emod_lt_of_pos i (by norm_num)
      have hklt : (i % 4).toNat < 4 := by
        have hcast := Int.toNat_of_nonneg h0
        omega
      refine ⟨(⟨(i % 4).toNat, hklt⟩, false), Subtype.ext ?_⟩
      simp only [u_F]
      rw [show (((i % 4).toNat : ℕ) : ℤ) = i % 4 from by
            rw [Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))]]
      rw [hi, ← zpow_mod_orderOf (z * g) i, u_orderOf_A h]
      norm_num
    · have h0 : 0 ≤ i % 4 := Int.emod_nonneg i (by norm_num)
      have h4 : i % 4 < 4 := Int.emod_lt_of_pos i (by norm_num)
      have hklt : (i % 4).toNat < 4 := by
        have hcast := Int.toNat_of_nonneg h0
        omega
      refine ⟨(⟨(i % 4).toNat, hklt⟩, true), Subtype.ext ?_⟩
      simp only [u_F]
      rw [show (((i % 4).toNat : ℕ) : ℤ) = i % 4 from by
            rw [Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))]]
      rw [hi, ← zpow_mod_orderOf (z * g) i, u_orderOf_A h]
      norm_num

theorem card (h : D8Rel z g x) : Nat.card (closure ({z, g} : Set G)) = 8 := by
  rw [← Nat.card_eq_of_bijective (u_F h) (u_F_bijective h)]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

end D8Rel

end CFSG.OddStandard.AltStdSec.SwapPartner
