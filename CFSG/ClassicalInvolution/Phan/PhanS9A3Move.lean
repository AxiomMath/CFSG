module

public import CFSG.ClassicalInvolution.Phan.PhanS9A1Act

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

namespace A0

section Move

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem card_F_ne_zero (D : KDat F K) : Nat.card F ≠ 0 := by
  intro h0
  have h := D.tau_pow 0
  rw [h0, pow_zero, map_zero] at h
  exact zero_ne_one h

theorem finite_F (D : KDat F K) : Finite F := Nat.finite_of_card_ne_zero (card_F_ne_zero D)

theorem finite_K (D : KDat F K) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [D.card_K]; exact pow_ne_zero 2 (card_F_ne_zero D))

theorem exists_norm_eq (D : KDat F K) {δ : F} (hδ : δ ≠ 0) :
    ∃ m : K, m * D.τ m = algebraMap F K δ := by
  classical
  have := finite_F D
  have := finite_K D
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  have hδK : algebraMap F K δ ≠ 0 := fun h =>
    hδ ((map_eq_zero_iff _ (algebraMap F K).injective).mp h)
  have h := D.card_norm_fibre hδK (D.tau_alg δ)
  have hpos : 0 < (Finset.univ.filter fun m : K => m * D.τ m = algebraMap F K δ).card := by
    rw [h]
    exact Nat.succ_pos _
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hpos
  exact ⟨m, (Finset.mem_filter.mp hm).2⟩

theorem exists_comp (D : KDat F K) (h2K : (2 : K) ≠ 0) (v : K) :
    ∃ p q : F, v = algebraMap F K p + D.θ * algebraMap F K q := by
  have hτ2 : D.τ (2 : K) = 2 := map_ofNat D.τ 2
  have h : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2K
  obtain ⟨p, hp⟩ := D.fixed ((v + D.τ v) / 2) (by
    rw [map_div₀, map_add, D.tau_tau, hτ2]
    ring)
  obtain ⟨q, hq⟩ := D.fixed (D.θ * (D.τ v - v) / 2) (by
    rw [map_div₀, map_mul, map_sub, D.tau_tau, D.tau_theta, hτ2]
    ring)
  refine ⟨p, q, ?_⟩
  rw [hp, hq]
  linear_combination (-((D.τ v - v) / 2)) * D.theta_sq - v * h

theorem conjV_mk7 (D : KDat F K) (x0 x1 x2 y0 y1 y2 z : K) :
    conjV D (mk7 x0 x1 x2 y0 y1 y2 z) =
      mk7 (D.τ x0) (D.τ x1) (D.τ x2) (D.τ y0) (D.τ y1) (D.τ y2) (D.τ z) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [conjV_apply, mk7]
  · fin_cases i <;> simp [conjV_apply, mk7]
  · simp [conjV_apply, mk7]

theorem hrm_comb (D : KDat F K) (α β : K) :
    hrm D (α • vXi D + β • vE2 D) (α • vXi D + β • vE2 D) =
      4 * (α * D.τ α - β * D.τ β) := by
  have hy : α • vXi D + β • vE2 D =
      mk7 α β (-(β * D.θ)) α (-β) (β * D.θ) (α * D.θ) := by
    funext s
    rcases s with i | i | ⟨⟩
    · fin_cases i <;> simp [vXi, vE2, mk7]
    · fin_cases i <;> simp [vXi, vE2, mk7]
    · simp [vXi, vE2, mk7]
  rw [hy, hrm, conjV_mk7, polar_mk7]
  simp only [map_neg, map_mul, D.tau_theta]
  linear_combination (2 * β * D.τ β - 2 * α * D.τ α) * D.theta_sq

end Move

end A0

section Targets

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (h2 : (2 : F) ≠ 0)

theorem exists_La0_move (α β : K) (hff : IsFF7 D (α • vXi D + β • vE2 D)) :
    ∃ A : SL(2, F), ∃ c : K, c ≠ 0 ∧
      extK (La0 h2 A).toLinearMap (vXi D) = c • (α • vXi D + β • vE2 D) := by
  have h2K : (2 : K) ≠ 0 := A0.two_ne_zero_of h2
  have hN := A0.hrm_comb D α β
  have hne : α * D.τ α - β * D.τ β ≠ 0 := by
    intro h0
    apply hff.2
    rw [hN, h0, mul_zero]
  have hfix : D.τ (α * D.τ α - β * D.τ β) = α * D.τ α - β * D.τ β := by
    rw [map_sub, map_mul, map_mul, D.tau_tau, D.tau_tau]
    ring
  obtain ⟨δ, hδ⟩ := D.fixed _ hfix
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    apply hne
    rw [← hδ, map_zero]
  obtain ⟨m, hm⟩ := A0.exists_norm_eq D (inv_ne_zero hδ0)
  obtain ⟨α1, α2, hα⟩ := A0.exists_comp D h2K (m * α)
  obtain ⟨β1, β2, hβ⟩ := A0.exists_comp D h2K (m * β)
  have e1 : (m * α) * D.τ (m * α) = algebraMap F K (α1 ^ 2 + α2 ^ 2) := by
    rw [hα]
    simp only [map_add, map_mul, map_pow, D.tau_alg, D.tau_theta]
    linear_combination (-(algebraMap F K α2 ^ 2)) * D.theta_sq
  have e2 : (m * β) * D.τ (m * β) = algebraMap F K (β1 ^ 2 + β2 ^ 2) := by
    rw [hβ]
    simp only [map_add, map_mul, map_pow, D.tau_alg, D.tau_theta]
    linear_combination (-(algebraMap F K β2 ^ 2)) * D.theta_sq
  have e3 : (m * α) * D.τ (m * α) - (m * β) * D.τ (m * β) =
      (m * D.τ m) * (α * D.τ α - β * D.τ β) := by
    simp only [map_mul]
    ring
  have hdet : α1 ^ 2 + α2 ^ 2 - (β1 ^ 2 + β2 ^ 2) = 1 := by
    apply (algebraMap F K).injective
    rw [map_sub, ← e1, ← e2, e3, hm, ← hδ, ← map_mul, inv_mul_cancel₀ hδ0]
  have hA : (!![α1 + β1, α2 + β2; β2 - α2, α1 - β1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet
  let A : SL(2, F) := ⟨!![α1 + β1, α2 + β2; β2 - α2, α1 - β1], hA⟩
  have hAc : (A : Matrix (Fin 2) (Fin 2) F) = !![α1 + β1, α2 + β2; β2 - α2, α1 - β1] := rfl
  refine ⟨A, m, ?_, ?_⟩
  · intro hm0
    rw [hm0, zero_mul] at hm
    exact inv_ne_zero hδ0 ((map_eq_zero_iff _ (algebraMap F K).injective).mp hm.symm)
  · rw [A0.La0_vXi_pqrs D h2 A α1 α2 β1 β2 hAc, ← hα, ← hβ, smul_add, smul_smul, smul_smul]

end Targets

end CFSG.ClassicalInvolution.PhanB3.S
