module

public import CFSG.ClassicalInvolution.Phan.PhanS9B2Rot

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

namespace HA1

section Decomp

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

include D in
theorem finite_of_kdat : Finite F ∧ Finite K := by
  have h0 : Nat.card F ≠ 0 := by
    intro h
    have := D.tau_pow 0
    rw [map_zero, h, pow_zero] at this
    exact zero_ne_one this
  refine ⟨Nat.finite_of_card_ne_zero h0, Nat.finite_of_card_ne_zero ?_⟩
  rw [D.card_K]
  exact pow_ne_zero 2 h0

theorem exists_norm_eq {n : K} (hn0 : n ≠ 0) (hn : D.τ n = n) : ∃ l : K, l * D.τ l = n := by
  obtain ⟨hF, hK⟩ := finite_of_kdat D
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  classical
  have h := D.card_norm_fibre hn0 hn
  have hpos : 0 < (Finset.univ.filter fun m : K => m * D.τ m = n).card := by
    rw [h]
    exact Nat.succ_pos _
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  exact ⟨l, (Finset.mem_filter.mp hl).2⟩

theorem exists_decomp (h2 : (2 : F) ≠ 0) (z : K) :
    ∃ z₁ z₂ : F, z = algebraMap F K z₁ + algebraMap F K z₂ * D.θ := by
  have h2K := two_ne_zero_K (K := K) h2
  have hθ0 := theta_ne_zero D
  obtain ⟨z₁, hz₁⟩ := D.fixed ((z + D.τ z) / 2) (by
    rw [map_div₀, map_add, D.tau_tau, map_ofNat]
    ring)
  obtain ⟨z₂, hz₂⟩ := D.fixed ((z - D.τ z) / (2 * D.θ)) (by
    rw [map_div₀, map_sub, D.tau_tau, map_mul, map_ofNat, D.tau_theta]
    field_simp
    ring)
  refine ⟨z₁, z₂, ?_⟩
  rw [hz₁, hz₂]
  field_simp
  ring

theorem exists_decomp_left (h2 : (2 : F) ≠ 0) (z : K) :
    ∃ a b : F, z = algebraMap F K a - 2 * algebraMap F K b * D.θ := by
  have h2K := two_ne_zero_K (K := K) h2
  obtain ⟨z₁, z₂, hz⟩ := exists_decomp D h2 z
  refine ⟨z₁, -(z₂ / 2), ?_⟩
  rw [hz]
  simp only [map_neg, map_div₀, map_ofNat]
  field_simp
  ring

theorem exists_decomp_right (h2 : (2 : F) ≠ 0) (z : K) :
    ∃ c d : F, z = -algebraMap F K d - algebraMap F K c * D.θ / 2 := by
  have h2K := two_ne_zero_K (K := K) h2
  obtain ⟨z₁, z₂, hz⟩ := exists_decomp D h2 z
  refine ⟨-(2 * z₂), -z₁, ?_⟩
  rw [hz]
  simp only [map_neg, map_mul, map_ofNat]
  field_simp
  ring

end Decomp

section Entries

variable {F : Type} [Field F]

theorem exists_SL_of_entries (a b c d : F) (h : a * d - b * c = 1) :
    ∃ A : SL(2, F), A 0 0 = a ∧ A 0 1 = b ∧ A 1 0 = c ∧ A 1 1 = d :=
  ⟨⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩, rfl, rfl, rfl, rfl⟩

end Entries

section Conj

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem conjV_mk7 (x0 x1 x2 y0 y1 y2 z : K) :
    conjV D (mk7 x0 x1 x2 y0 y1 y2 z) =
      mk7 (D.τ x0) (D.τ x1) (D.τ x2) (D.τ y0) (D.τ y1) (D.τ y2) (D.τ z) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

end Conj

end HA1

section Main

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem exists_La1_move (α β : K) (hff : IsFF7 D (α • vE2 D + β • vE3 D)) :
    ∃ A : SL(2, F), ∃ c : K, c ≠ 0 ∧
      extK (La1 h2 A).toLinearMap (vE2 D) = c • (α • vE2 D + β • vE3 D) := by
  have h2K := HA1.two_ne_zero_K (K := K) h2
  have hθ := D.theta_sq
  have hy := HA1.add_vE23 D α β
  have hhrm : hrm D (α • vE2 D + β • vE3 D) (α • vE2 D + β • vE3 D) =
      2 * ((α + β) * D.τ (β - α) + D.τ (α + β) * (β - α)) := by
    rw [hy, hrm, HA1.conjV_mk7, polar_mk7]
    simp only [map_zero, map_mul, D.tau_theta]
    linear_combination (-((β - α) * D.τ (α + β) + (α + β) * D.τ (β - α))) * hθ
  set p : K := α + β with hp
  set s : K := β - α with hs
  set T : K := p * D.τ s + D.τ p * s with hT
  have hT0 : T ≠ 0 := fun h => hff.2 (by rw [hhrm, h, mul_zero])
  have hTfix : D.τ T = T := by
    rw [hT, map_add, map_mul, map_mul, D.tau_tau, D.tau_tau]
    ring
  have hn0 : -(2 * T⁻¹) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h2K (inv_ne_zero hT0))
  have hnfix : D.τ (-(2 * T⁻¹)) = -(2 * T⁻¹) := by
    rw [map_neg, map_mul, map_ofNat, map_inv₀, hTfix]
  obtain ⟨l, hl⟩ := HA1.exists_norm_eq D hn0 hnfix
  have hl0 : l ≠ 0 := fun h => hn0 (by rw [← hl, h, zero_mul])
  obtain ⟨a, b, hu⟩ := HA1.exists_decomp_left D h2 (l * p)
  obtain ⟨c, d, hw⟩ := HA1.exists_decomp_right D h2 (l * s)
  have hi : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2K
  have hdetK : algebraMap F K a * algebraMap F K d -
      algebraMap F K b * algebraMap F K c = 1 := by
    have e1 : (l * p) * D.τ (l * s) + D.τ (l * p) * (l * s) = (l * D.τ l) * T := by
      rw [hT, map_mul, map_mul]
      ring
    have e2 : (l * p) * D.τ (l * s) + D.τ (l * p) * (l * s) =
        -2 * (algebraMap F K a * algebraMap F K d - algebraMap F K b * algebraMap F K c) := by
      rw [hu, hw]
      simp only [map_sub, map_neg, map_mul, map_div₀, map_ofNat, D.tau_alg, D.tau_theta]
      linear_combination (-2 * algebraMap F K b * algebraMap F K c) * hθ +
        (-2 * algebraMap F K b * algebraMap F K c * D.θ ^ 2) * hi
    have e3 : (l * D.τ l) * T = -2 := by
      rw [hl, neg_mul, mul_assoc, inv_mul_cancel₀ hT0, mul_one]
    exact mul_left_cancel₀ (neg_ne_zero.mpr h2K) (by linear_combination e1 + e3 - e2)
  obtain ⟨A, hA00, hA01, hA10, hA11⟩ := HA1.exists_SL_of_entries a b c d (by
    apply (algebraMap F K).injective
    rw [map_sub, map_mul, map_mul, map_one]
    exact hdetK)
  refine ⟨A, l, hl0, ?_⟩
  rw [HA1.extK_La1_vE2, hy, HA1.smul_mk7, HA1.mk7_eq_iff, hA00, hA01, hA10, hA11]
  refine ⟨by ring, hu.symm, ?_, by ring, hw.symm, ?_, by ring⟩
  · linear_combination (-D.θ) * hw
  · linear_combination (-D.θ) * hu

end Main

end CFSG.ClassicalInvolution.PhanB3.S
