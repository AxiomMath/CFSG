module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Quat

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

open Subgroup

variable {G : Type*} [Group G]

namespace QG

variable {a b : G} {N : ℕ}

theorem akb_sq (h : QG a b N) (k : ℕ) : a ^ k * b * (a ^ k * b) = a ^ N := by
  calc a ^ k * b * (a ^ k * b) = a ^ k * (b * a ^ k) * b := by group
    _ = a ^ k * ((a ^ k)⁻¹ * b) * b := by rw [h.b_pow]
    _ = b * b := by group
    _ = a ^ N := h.bsq

theorem akb_inv (h : QG a b N) (k : ℕ) {x : G} (hx : x ∈ zpowers a) :
    a ^ k * b * x * (a ^ k * b)⁻¹ = x⁻¹ := by
  have h1 := h.b_inv_zpowers hx
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
  have hc : Commute (a ^ k) (a ^ j) := ((Commute.refl a).pow_left k).zpow_right j
  calc a ^ k * b * a ^ j * (a ^ k * b)⁻¹ = a ^ k * (b * a ^ j * b⁻¹) * (a ^ k)⁻¹ := by group
    _ = a ^ k * (a ^ j)⁻¹ * (a ^ k)⁻¹ := by rw [h1]
    _ = (a ^ j)⁻¹ := by rw [hc.inv_right.eq]; group

theorem not_comm (h : QG a b N) (hN : 2 ≤ N) : a * b ≠ b * a := by
  intro hab
  have h1 : a⁻¹ * b = a * b := by rw [← h.bcomm]; exact hab.symm
  have h2 : a⁻¹ = a := mul_right_cancel h1
  have h3 : a ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [← h2]; exact inv_mul_cancel a
  have := orderOf_dvd_of_pow_eq_one h3
  rw [h.ord] at this
  have := Nat.le_of_dvd (by omega) this
  omega

theorem center_cases (h : QG a b N) (hN : 2 ≤ N) {P : Subgroup G} (ha : a ∈ P) (hb : b ∈ P)
    (hgen : ∀ x ∈ P, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b) {x : G} (hx : x ∈ P)
    (hc : ∀ y ∈ P, x * y = y * x) : x = 1 ∨ x = a ^ N := by
  obtain ⟨k, hk | hk⟩ := hgen x hx
  · subst hk
    have hcb := hc b hb
    have h1 : a ^ k * b = (a ^ k)⁻¹ * b := by rw [← h.b_pow]; exact hcb
    have h2 : a ^ k = (a ^ k)⁻¹ := mul_right_cancel h1
    have h3 : a ^ k * a ^ k = 1 := by
      nth_rewrite 1 [h2]; exact inv_mul_cancel _
    by_cases h4 : a ^ k = 1
    · exact Or.inl h4
    · exact Or.inr (h.eq_aN_of_involution (by omega) hgen hx h3 h4)
  · exfalso
    subst hk
    have hca := hc a ha
    have h1 : a ^ k * b * a = a * (a ^ k * b) := hca
    have h2 : a ^ k * (a⁻¹ * b) = a ^ k * (a * b) := by
      calc a ^ k * (a⁻¹ * b) = a ^ k * (b * a) := by rw [h.bcomm]
        _ = a ^ k * b * a := by group
        _ = a * (a ^ k * b) := h1
        _ = a ^ k * (a * b) := by
          rw [← mul_assoc, ← mul_assoc, ((Commute.refl a).pow_left k).eq.symm]
    have h3 : a⁻¹ * b = a * b := mul_left_cancel h2
    have h4 : a⁻¹ = a := mul_right_cancel h3
    have h5 : a ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [← h4]; exact inv_mul_cancel a
    have := orderOf_dvd_of_pow_eq_one h5
    rw [h.ord] at this
    have := Nat.le_of_dvd (by omega) this
    omega

theorem not_isCyclic (h : QG a b N) (hN : 2 ≤ N) {P : Subgroup G} (ha : a ∈ P) (hb : b ∈ P) :
    ¬ IsCyclic ↥P := by
  intro hP
  have := hP.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact h.not_comm hN (congrArg Subtype.val this)

end QG

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q
