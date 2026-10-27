module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.IVK.DihedralAux

open DihedralGroup

theorem two_mul_eq_zero_iff' {k : ℕ} [NeZero k] (i : ZMod k) (h : i + i = 0) :
    i = 0 ∨ i = ((k / 2 : ℕ) : ZMod k) := by
  have hneg : -i = i := neg_eq_of_add_eq_zero_right h
  rcases (ZMod.neg_eq_self_iff i).mp hneg with h0 | h1
  · left; exact h0
  · right
    have hk2 : k % 2 = 0 := by
      have := ZMod.val_lt i
      omega
    rw [← ZMod.natCast_zmod_val i]
    congr 1
    omega

theorem exists_mul_of_involutions {D : Type*} [Group D] {n : ℕ} (φ : D ≃* DihedralGroup n)
    (x : D) :
    ∃ a b : D, (a = 1 ∨ orderOf a = 2) ∧ (b = 1 ∨ orderOf b = 2) ∧ x = a * b := by
  obtain ⟨y, rfl⟩ := φ.symm.surjective x
  rcases y with k | k
  · refine ⟨φ.symm (sr 0), φ.symm (sr k), Or.inr ?_, Or.inr ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]; exact orderOf_sr 0
    · rw [MulEquiv.orderOf_eq]; exact orderOf_sr k
    · rw [← map_mul, sr_mul_sr]; simp
  · exact ⟨1, φ.symm (sr k), Or.inl rfl, Or.inr (by rw [MulEquiv.orderOf_eq]; exact orderOf_sr k),
      by simp⟩

theorem le_of_involutions_le {G : Type*} [Group G] (D H : Subgroup G) {n : ℕ}
    (φ : ↥D ≃* DihedralGroup n) (h : ∀ x ∈ D, orderOf x = 2 → x ∈ H) : D ≤ H := by
  intro x hx
  obtain ⟨a, b, ha, hb, hab⟩ := exists_mul_of_involutions φ ⟨x, hx⟩
  have hmem : ∀ c : ↥D, (c = 1 ∨ orderOf c = 2) → (c : G) ∈ H := by
    rintro c (rfl | hc)
    · exact H.one_mem
    · exact h c c.2 (by rw [Subgroup.orderOf_coe]; exact hc)
  have : x = (a : G) * (b : G) := by
    have := congrArg Subtype.val hab
    simpa using this
  rw [this]
  exact H.mul_mem (hmem a ha) (hmem b hb)

theorem eq_sq_of_comm_dihedral {n : ℕ} [NeZero n] {c f : DihedralGroup n} (hco : orderOf c = 4)
    (hfo : orderOf f = 2) (hcomm : f * c = c * f) : f = c ^ 2 := by
  have hc2 : c ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hco] at this
    omega
  have hc4 : c ^ 4 = 1 := by rw [← hco]; exact pow_orderOf_eq_one c
  have hf1 : f ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hfo
    omega
  have hf2 : f ^ 2 = 1 := by rw [← hfo]; exact pow_orderOf_eq_one f
  rcases c with a | a
  · rcases f with b | b
    · have hb2 : b + b = 0 := by
        rw [pow_two, r_mul_r, one_def] at hf2
        exact r.inj hf2
      have hb0 : b ≠ 0 := by
        intro h
        apply hf1
        rw [h, one_def]
      have ha2 : a + a ≠ 0 := by
        intro h
        apply hc2
        rw [pow_two, r_mul_r, h, one_def]
      have ha4 : (a + a) + (a + a) = 0 := by
        have : (r a : DihedralGroup n) ^ 4 = r (a + a + (a + a)) := by
          rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, r_mul_r, r_mul_r]
        rw [this, one_def] at hc4
        exact r.inj hc4
      have hb : b = ((n / 2 : ℕ) : ZMod n) := (two_mul_eq_zero_iff' b hb2).resolve_left hb0
      have ha : a + a = ((n / 2 : ℕ) : ZMod n) :=
        (two_mul_eq_zero_iff' (a + a) ha4).resolve_left ha2
      rw [pow_two, r_mul_r, hb, ha]
    · exfalso
      rw [sr_mul_r, r_mul_sr] at hcomm
      have h := sr.inj hcomm
      apply hc2
      rw [pow_two, r_mul_r, one_def]
      congr 1
      linear_combination h
  · rw [orderOf_sr] at hco
    omega

theorem involution_mem_zpowers_of_comm {D : Type*} [Group D] {n : ℕ} [NeZero n]
    (φ : D ≃* DihedralGroup n) {c f : D} (hc : orderOf c = 4) (hf : orderOf f = 2)
    (hcomm : f * c = c * f) : f ∈ Subgroup.zpowers c := by
  have h := eq_sq_of_comm_dihedral (c := φ c) (f := φ f) (by rw [MulEquiv.orderOf_eq]; exact hc)
    (by rw [MulEquiv.orderOf_eq]; exact hf) (by rw [← map_mul, ← map_mul, hcomm])
  have : f = c ^ 2 := φ.injective (by rw [h, map_pow])
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) 2

theorem exists_orderOf_eq_four {k : ℕ} [NeZero k] (h4 : 4 ∣ k) :
    ∃ c : DihedralGroup k, orderOf c = 4 := by
  obtain ⟨j, rfl⟩ := h4
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      exact absurd (by simp) (NeZero.ne (4 * 0))
    · exact h
  refine ⟨r ((j : ℕ) : ZMod (4 * j)), ?_⟩
  rw [orderOf_r]
  have hval : (((j : ℕ) : ZMod (4 * j)).val) = j := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [hval, Nat.gcd_eq_right (Dvd.intro_left 4 rfl)]
  rw [Nat.mul_div_cancel _ hj]

end CFSG.GH74.GLS.IVK.DihedralAux
