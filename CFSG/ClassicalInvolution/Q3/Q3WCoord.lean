module

public import CFSG.ClassicalInvolution.Q3.Q3WFin
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem xp_mul (s t : K) : xp s * xp t = xp (s + t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xp, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem xm_mul (s t : K) : xm s * xm t = xm (s + t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xm, Matrix.mul_apply, Fin.sum_univ_two]

theorem xp_zero : (xp (0 : K)) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xp]

theorem xm_zero : (xm (0 : K)) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xm]

theorem xp_inv (t : K) : (xp t)⁻¹ = xp (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [xp_mul, add_neg_cancel, xp_zero])

theorem xm_inv (t : K) : (xm t)⁻¹ = xm (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [xm_mul, add_neg_cancel, xm_zero])

theorem xp_ne_one {t : K} (ht : t ≠ 0) : xp t ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [xp] at this
  exact ht this

theorem xm_ne_one {t : K} (ht : t ≠ 0) : xm t ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp [xm] at this
  exact ht this

theorem eq_zero_of_xp_eq_one {t : K} (h : xp t = 1) : t = 0 := by
  by_contra ht
  exact xp_ne_one ht h

theorem eq_zero_of_xm_eq_one {t : K} (h : xm t = 1) : t = 0 := by
  by_contra ht
  exact xm_ne_one ht h

theorem rotSL_xp (t : K) : (rotSL : SL(2, K)) * xp t * rotSL⁻¹ = xm (-t) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotSL, xp, xm, CFSG.ClassicalInvolution.Phan.rotMat,
      CFSG.ClassicalInvolution.Phan.rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotSL_xm (t : K) : (rotSL : SL(2, K)) * xm t * rotSL⁻¹ = xp (-t) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotSL, xp, xm, CFSG.ClassicalInvolution.Phan.rotMat,
      CFSG.ClassicalInvolution.Phan.rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotSL_inv_xp (t : K) : (rotSL : SL(2, K))⁻¹ * xp t * rotSL = xm (-t) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotSL, xp, xm, CFSG.ClassicalInvolution.Phan.rotMat,
      CFSG.ClassicalInvolution.Phan.rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotSL_inv_xm (t : K) : (rotSL : SL(2, K))⁻¹ * xm t * rotSL = xp (-t) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotSL, xp, xm, CFSG.ClassicalInvolution.Phan.rotMat,
      CFSG.ClassicalInvolution.Phan.rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

variable (K) in
@[expose] def coordSet : Set SL(2, K) := {g | g ≠ 1 ∧ ∃ t : K, g = xp t ∨ g = xm t}

theorem xp_mem_coordSet {t : K} (ht : t ≠ 0) : xp t ∈ coordSet K :=
  ⟨xp_ne_one ht, t, Or.inl rfl⟩

theorem xm_mem_coordSet {t : K} (ht : t ≠ 0) : xm t ∈ coordSet K :=
  ⟨xm_ne_one ht, t, Or.inr rfl⟩

theorem inv_mem_coordSet {g : SL(2, K)} (hg : g ∈ coordSet K) : g⁻¹ ∈ coordSet K := by
  obtain ⟨hne, t, h | h⟩ := hg
  · have ht : t ≠ 0 := fun h0 => hne (by rw [h, h0, xp_zero])
    rw [h, xp_inv]
    exact xp_mem_coordSet (neg_ne_zero.mpr ht)
  · have ht : t ≠ 0 := fun h0 => hne (by rw [h, h0, xm_zero])
    rw [h, xm_inv]
    exact xm_mem_coordSet (neg_ne_zero.mpr ht)

theorem coordSet_cases {g : SL(2, K)} (hg : g ∈ coordSet K) :
    ∃ t : K, t ≠ 0 ∧ (g = xp t ∨ g = xm t) := by
  obtain ⟨hne, t, h | h⟩ := hg
  · exact ⟨t, fun h0 => hne (by rw [h, h0, xp_zero]), Or.inl h⟩
  · exact ⟨t, fun h0 => hne (by rw [h, h0, xm_zero]), Or.inr h⟩

theorem coordSet_finite [Finite K] : (coordSet K).Finite := Set.toFinite _

theorem image_coordSet_eq [Finite K] (γ : SL(2, K) ≃* SL(2, K))
    (h : ∀ g ∈ coordSet K, γ g ∈ coordSet K) : γ '' coordSet K = coordSet K := by
  refine Set.eq_of_subset_of_ncard_le (by rintro _ ⟨g, hg, rfl⟩; exact h g hg) ?_ coordSet_finite
  rw [Set.ncard_image_of_injective _ γ.injective]

theorem map_xp (ψ : K ≃+* K) (t : K) :
    Matrix.SpecialLinearGroup.map (ψ : K →+* K) (xp t) = xp (ψ t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xp, RingHom.mapMatrix_apply]

theorem map_xm (ψ : K ≃+* K) (t : K) :
    Matrix.SpecialLinearGroup.map (ψ : K →+* K) (xm t) = xm (ψ t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xm, RingHom.mapMatrix_apply]

theorem fieldAutSL_xp (ψ : K ≃+* K) (t : K) : fieldAutSL ψ 2 (xp t) = xp (ψ t) :=
  map_xp ψ t

theorem fieldAutSL_xm (ψ : K ≃+* K) (t : K) : fieldAutSL ψ 2 (xm t) = xm (ψ t) :=
  map_xm ψ t

theorem diagConj2_xp (a b : Kˣ) (t : K) :
    diagConj2 a b (xp t) = xp ((a : K) * ((b⁻¹ : Kˣ) : K) * t) := by
  refine Subtype.ext ?_
  rw [coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xp, Matrix.mul_apply, Matrix.diagonal_apply]
  ring

theorem diagConj2_xm (a b : Kˣ) (t : K) :
    diagConj2 a b (xm t) = xm ((b : K) * ((a⁻¹ : Kˣ) : K) * t) := by
  refine Subtype.ext ?_
  rw [coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xm, Matrix.mul_apply, Matrix.diagonal_apply]
  ring

theorem invTransposeSL_xp (t : K) : invTransposeSL 2 (xp t) = xm (-t) := by
  refine Subtype.ext ?_
  rw [coe_invTransposeSL, xp_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xp, xm]

theorem invTransposeSL_xm (t : K) : invTransposeSL 2 (xm t) = xp (-t) := by
  refine Subtype.ext ?_
  rw [coe_invTransposeSL, xm_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xp, xm]

theorem fieldAutSL_coord (ψ : K ≃+* K) {g : SL(2, K)} (hg : g ∈ coordSet K) :
    fieldAutSL ψ 2 g ∈ coordSet K := by
  obtain ⟨t, ht, h | h⟩ := coordSet_cases hg
  · rw [h, fieldAutSL_xp]
    exact xp_mem_coordSet (by simpa using ht)
  · rw [h, fieldAutSL_xm]
    exact xm_mem_coordSet (by simpa using ht)

theorem diagConj2_coord (a b : Kˣ) {g : SL(2, K)} (hg : g ∈ coordSet K) :
    diagConj2 a b g ∈ coordSet K := by
  obtain ⟨t, ht, h | h⟩ := coordSet_cases hg
  · rw [h, diagConj2_xp]
    exact xp_mem_coordSet (mul_ne_zero (mul_ne_zero a.ne_zero (b⁻¹).ne_zero) ht)
  · rw [h, diagConj2_xm]
    exact xm_mem_coordSet (mul_ne_zero (mul_ne_zero b.ne_zero (a⁻¹).ne_zero) ht)

theorem invTransposeSL_coord {g : SL(2, K)} (hg : g ∈ coordSet K) :
    invTransposeSL 2 g ∈ coordSet K := by
  obtain ⟨t, ht, h | h⟩ := coordSet_cases hg
  · rw [h, invTransposeSL_xp]
    exact xm_mem_coordSet (neg_ne_zero.mpr ht)
  · rw [h, invTransposeSL_xm]
    exact xp_mem_coordSet (neg_ne_zero.mpr ht)

theorem rotConj_coord {g : SL(2, K)} (hg : g ∈ coordSet K) :
    (rotSL : SL(2, K)) * g * rotSL⁻¹ ∈ coordSet K := by
  obtain ⟨t, ht, h | h⟩ := coordSet_cases hg
  · rw [h, rotSL_xp]
    exact xm_mem_coordSet (neg_ne_zero.mpr ht)
  · rw [h, rotSL_xm]
    exact xp_mem_coordSet (neg_ne_zero.mpr ht)

theorem rotConj_inv_coord {g : SL(2, K)} (hg : g ∈ coordSet K) :
    (rotSL : SL(2, K))⁻¹ * g * rotSL ∈ coordSet K := by
  obtain ⟨t, ht, h | h⟩ := coordSet_cases hg
  · rw [h, rotSL_inv_xp]
    exact xm_mem_coordSet (neg_ne_zero.mpr ht)
  · rw [h, rotSL_inv_xm]
    exact xp_mem_coordSet (neg_ne_zero.mpr ht)

end CFSG.ClassicalInvolution.Q3.Q3W
