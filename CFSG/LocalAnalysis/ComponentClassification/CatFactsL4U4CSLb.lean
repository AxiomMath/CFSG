module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL

variable {F : Type} [Field F]

theorem mul_map_eq_of_map (h4 : (4 : F) ≠ 0) (B : GL (Fin 4) F) (σ : F ≃+* F)
    (u v : SpecialLinearGroup (Fin 4) F) (hu : (u : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (hσv : ((v : Matrix (Fin 4) (Fin 4) F).map σ).trace = 4)
    (h : (conjAut 4 F B * fieldAut 4 F σ) (proj 4 F v) = proj 4 F u) :
    (B : Matrix (Fin 4) (Fin 4) F) * (v : Matrix (Fin 4) (Fin 4) F).map σ = u * B := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
  have hBB : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : ((CatalogueBHigherLinearAction.slConjugation 4 F B
      (SpecialLinearGroup.map σ.toRingHom v) : SpecialLinearGroup (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F).trace = 4 := by
    rw [coe_slConjugation, Matrix.trace_mul_cycle, hBB, Matrix.one_mul,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    exact hσv
  have e := coe_eq_of_proj_eq_of_trace h4 h htr hu
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at e
  calc (B : Matrix (Fin 4) (Fin 4) F) * (v : Matrix (Fin 4) (Fin 4) F).map σ =
      (B : Matrix (Fin 4) (Fin 4) F) * (v : Matrix (Fin 4) (Fin 4) F).map σ.toRingHom *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B := by
          rw [Matrix.mul_assoc _ _ (B : Matrix (Fin 4) (Fin 4) F), hBB, Matrix.mul_one]; rfl
    _ = u * B := by rw [e]

theorem cancel_mZ {l : F} (hll : l * l = 1) {X Y : Matrix (Fin 4) (Fin 4) F}
    (h : X * mZ l = Y * mZ l) : X = Y := by
  have := congrArg (· * mZ l) h
  simp only [Matrix.mul_assoc, mZ_mul_mZ hll, Matrix.mul_neg, Matrix.mul_one, neg_inj] at this
  exact this

theorem eq_of_mem_CA_dual (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1) (hll : l * l = 1)
    (B : GL (Fin 4) F) (σ : F ≃+* F) (hσl : σ l = l)
    (hg : conjAut 4 F B * fieldAut 4 F σ * dualAut 4 F ∈ CA F hl) :
    (∀ c, σ c = c) ∧ ∃ a b : F, (B : Matrix (Fin 4) (Fin 4) F) = eK l a b * mZ l := by
  set B' : Matrix (Fin 4) (Fin 4) F := -((B : Matrix (Fin 4) (Fin 4) F) * mZ l) with hB'
  have hBB' : (B : Matrix (Fin 4) (Fin 4) F) = B' * mZ l := by
    rw [hB', Matrix.neg_mul, Matrix.mul_assoc, mZ_mul_mZ hll, Matrix.mul_neg, Matrix.mul_one,
      neg_neg]
  have key : ∀ (u : SpecialLinearGroup (Fin 4) F) (M M' : Matrix (Fin 4) (Fin 4) F),
      proj 4 F u ∈ JK F hl → (u : Matrix (Fin 4) (Fin 4) F) = M →
      (((u⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) = M' →
      (M : Matrix (Fin 4) (Fin 4) F).trace = 4 → (M'.map σ).trace = 4 →
      (B : Matrix (Fin 4) (Fin 4) F) * (M'.map σ)ᵀ = M * B := by
    intro u M M' hu hM hM' htr htr'
    have hfix : (conjAut 4 F B * fieldAut 4 F σ) (proj 4 F (u⁻¹).transpose) = proj 4 F u := by
      have := hg _ hu
      rwa [MulAut.mul_apply, dualAut_proj] at this
    have e := mul_map_eq_of_map h4 B σ u (u⁻¹).transpose (by rw [hM]; exact htr)
      (by rw [Matrix.SpecialLinearGroup.coe_transpose, hM', Matrix.transpose_map,
        Matrix.trace_transpose]; exact htr') hfix
    rw [Matrix.SpecialLinearGroup.coe_transpose, hM', Matrix.transpose_map, hM] at e
    exact e
  have hU : ∀ a b : F, B' * (uK l a b).map σ = uK l a b * B' := by
    intro a b
    have e := key (slUK l a b) (uK l a b) (uK l (-a) (-b)) ⟨_, slUK_mem_SK hl hl1 a b, rfl⟩ rfl
      (coe_slUK_inv l a b) (trace_uK l a b) (trace_map_uK σ l (-a) (-b))
    rw [map_uK σ hσl, hBB', Matrix.mul_assoc, map_neg, map_neg, mZ_uK,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc] at e
    rw [map_uK σ hσl]
    exact cancel_mZ hll e
  have hL : ∀ a b : F, B' * (lK l a b).map σ = lK l a b * B' := by
    intro a b
    have e := key (slLK l a b) (lK l a b) (lK l (-a) (-b)) ⟨_, slLK_mem_SK hl hl1 a b, rfl⟩ rfl
      (coe_slLK_inv l a b) (trace_lK l a b) (trace_map_lK σ l (-a) (-b))
    rw [map_lK σ hσl, hBB', Matrix.mul_assoc, map_neg, map_neg, mZ_lK,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc] at e
    rw [map_lK σ hσl]
    exact cancel_mZ hll e
  have hdet : IsUnit B'.det := by
    have h1 : IsUnit (B : Matrix (Fin 4) (Fin 4) F).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
    rw [hBB', Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨hσ, hB'eq⟩ := eq_of_semilinear_comm_uK hl hdet (σ : F →+* F) (hU 1 0) (hL 1 0)
    (hU 0 1) (fun c => hU c 0)
  refine ⟨hσ, B' 0 0, B' 1 0, ?_⟩
  rw [hBB', ← smul_one_add_smul_kZero, ← hB'eq]

theorem apply_of_mem_CA_dual (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    (hll : l * l = 1) (B : GL (Fin 4) F) (σ : F ≃+* F) (hσl : σ l = l)
    (hg : conjAut 4 F B * fieldAut 4 F σ * dualAut 4 F ∈ CA F hl)
    (U : SpecialLinearGroup (Fin 4) F) {a b : F}
    (hU : (U : Matrix (Fin 4) (Fin 4) F) = eK l a b) :
    (conjAut 4 F B * fieldAut 4 F σ * dualAut 4 F) (proj 4 F U) = (proj 4 F U)⁻¹ := by
  obtain ⟨hσ, a', b', hB⟩ := eq_of_mem_CA_dual h4 hl hl1 hll B σ hσl hg
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj, ← map_inv]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.coe_transpose]
  set V : Matrix (Fin 4) (Fin 4) F := ((U⁻¹ : SpecialLinearGroup (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) with hV
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F, M.map (σ : F →+* F) = M := fun M => by
    ext i j
    simp [hσ]
  rw [show (Vᵀ).map σ.toRingHom = Vᵀ from hmap _]
  have hVU : V * (U : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hV, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hUV : (U : Matrix (Fin 4) (Fin 4) F) * V = 1 := by
    rw [hV, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hVmZ : V * mZ l = mZ l * Vᵀ := by
    calc V * mZ l = V * mZ l * (V * (U : Matrix (Fin 4) (Fin 4) F))ᵀ := by
          rw [hVU, Matrix.transpose_one, Matrix.mul_one]
      _ = V * (mZ l * (U : Matrix (Fin 4) (Fin 4) F)ᵀ) * Vᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = V * ((U : Matrix (Fin 4) (Fin 4) F) * mZ l) * Vᵀ := by rw [hU, eK_mZ]
      _ = mZ l * Vᵀ := by rw [← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hcomm : eK l a' b' * V = V * eK l a' b' := by
    calc eK l a' b' * V = V * (U : Matrix (Fin 4) (Fin 4) F) * eK l a' b' * V := by
          rw [hVU, Matrix.one_mul]
      _ = V * (eK l a' b' * (U : Matrix (Fin 4) (Fin 4) F)) * V := by
          rw [hU, eK_comm]; simp only [Matrix.mul_assoc]
      _ = V * eK l a' b' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hUV, Matrix.mul_one]
  have hBB : (B : Matrix (Fin 4) (Fin 4) F) * ((B⁻¹ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (B : Matrix (Fin 4) (Fin 4) F) * Vᵀ * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      = eK l a' b' * (mZ l * Vᵀ) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [hB, Matrix.mul_assoc (eK l a' b')]
    _ = V * (B : Matrix (Fin 4) (Fin 4) F) *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← hVmZ, ← Matrix.mul_assoc, hcomm, hB, Matrix.mul_assoc V]
    _ = V := by rw [Matrix.mul_assoc, hBB, Matrix.mul_one]

end CSL

end CFSG.ComponentClassification.CatFactsL4U4
