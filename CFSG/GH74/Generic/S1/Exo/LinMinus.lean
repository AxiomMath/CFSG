module

public import CFSG.GH74.Generic.S1.Exo.Defs
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module QuadraticMap CFSG.Open
open scoped Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def glLinEquiv (K : Type) [Field K] :
    GL (Fin 4) K ≃* ((Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :=
  (Matrix.GeneralLinearGroup.toLin).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 4 → K))

theorem glLinEquiv_apply (k : GL (Fin 4) K) (v : Fin 4 → K) :
    glLinEquiv K k v = (k : Matrix (Fin 4) (Fin 4) K) *ᵥ v := by
  simp [glLinEquiv]

theorem glLinEquiv_neg_one : glLinEquiv K (-1) = LinearEquiv.neg K := by
  ext v i
  simp [glLinEquiv_apply, Matrix.neg_mulVec]

theorem coe_det_glLinEquiv (k : GL (Fin 4) K) :
    ((LinearEquiv.det (glLinEquiv K k) : Kˣ) : K) = (k : Matrix (Fin 4) (Fin 4) K).det := by
  rw [LinearEquiv.coe_det]
  have : ((glLinEquiv K k : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) =
      Matrix.toLin' (k : Matrix (Fin 4) (Fin 4) K) := by
    ext v i
    simp [glLinEquiv_apply, Matrix.toLin'_apply]
  rw [this, LinearMap.det_toLin']

theorem toQuadraticForm'_apply (G : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    Matrix.toQuadraticForm' G v = v ⬝ᵥ (G *ᵥ v) := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

theorem sym_eq_of_forall_quad (h2 : (2 : K) ≠ 0) {M G : Matrix (Fin 4) (Fin 4) K}
    (hM : Mᵀ = M) (hG : Gᵀ = G)
    (h : ∀ v, v ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (G *ᵥ v)) : M = G := by
  have key : ∀ (A : Matrix (Fin 4) (Fin 4) K), Aᵀ = A → ∀ i j : Fin 4,
      (Pi.single i 1 + Pi.single j 1 : Fin 4 → K) ⬝ᵥ (A *ᵥ (Pi.single i 1 + Pi.single j 1)) =
        A i i + 2 * A i j + A j j := by
    intro A hA i j
    have hij : A j i = A i j := by
      have := congrFun (congrFun hA i) j
      simpa [Matrix.transpose_apply] using this
    simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct, hij]
    ring
  have diag : ∀ (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4),
      (Pi.single i 1 : Fin 4 → K) ⬝ᵥ (A *ᵥ (Pi.single i 1)) = A i i := by
    intro A i
    simp
  ext i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  rw [key M hM, key G hG] at h1
  have h2i := h (Pi.single i 1)
  have h2j := h (Pi.single j 1)
  rw [diag, diag] at h2i h2j
  have : 2 * M i j = 2 * G i j := by linear_combination h1 - h2i - h2j
  exact mul_left_cancel₀ h2 this


theorem quad_comp_eq (G : Matrix (Fin 4) (Fin 4) K) (k : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    (k *ᵥ v) ⬝ᵥ (G *ᵥ (k *ᵥ v)) = v ⬝ᵥ ((kᵀ * G * k) *ᵥ v) := by
  have h : ∀ (u w : Fin 4 → K), (k *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (kᵀ *ᵥ w) := by
    intro u w
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem mem_soForm_iff_mem_soMat (h2 : (2 : K) ≠ 0) (G : Matrix (Fin 4) (Fin 4) K) (hsymm : Gᵀ = G)
    (k : GL (Fin 4) K) :
    glLinEquiv K k ∈ soForm (Matrix.toQuadraticForm' G) ↔ k ∈ soMat G := by
  rw [mem_soForm_iff, mem_soMat_iff]
  have hdet : LinearEquiv.det (glLinEquiv K k) = 1 ↔ (k : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [← coe_det_glLinEquiv]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact Units.ext h
  rw [hdet]
  refine and_congr_left fun _ => ?_
  have hq : ∀ v, Matrix.toQuadraticForm' G (glLinEquiv K k v) =
      v ⬝ᵥ (((k : Matrix (Fin 4) (Fin 4) K)ᵀ * G * (k : Matrix (Fin 4) (Fin 4) K)) *ᵥ v) := by
    intro v
    rw [toQuadraticForm'_apply, glLinEquiv_apply, quad_comp_eq]
  simp only [hq, toQuadraticForm'_apply]
  constructor
  · intro h
    refine sym_eq_of_forall_quad h2 ?_ hsymm h
    simp [Matrix.transpose_mul, hsymm, Matrix.mul_assoc]
  · intro h v
    rw [h]


theorem soMat_mulEquiv_soForm (h2 : (2 : K) ≠ 0) (G : Matrix (Fin 4) (Fin 4) K) (hsymm : Gᵀ = G) :
    ∃ ψ : soMat G ≃* soForm (Matrix.toQuadraticForm' G),
      ∀ k : soMat G, (k : GL (Fin 4) K) = -1 →
        ((ψ k : soForm (Matrix.toQuadraticForm' G)) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) =
          LinearEquiv.neg K := by
  have hmap : (soMat G).map (glLinEquiv K).toMonoidHom = soForm (Matrix.toQuadraticForm' G) := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (mem_soForm_iff_mem_soMat h2 G hsymm k).2 hk
    · intro hg
      refine ⟨(glLinEquiv K).symm g, ?_, by simp⟩
      have := (mem_soForm_iff_mem_soMat h2 G hsymm ((glLinEquiv K).symm g)).1
      exact this (by simpa using hg)
  let ψ : soMat G ≃* soForm (Matrix.toQuadraticForm' G) :=
    ((glLinEquiv K).subgroupMap (soMat G)).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨ψ, fun k hk => ?_⟩
  have : ((ψ k : soForm (Matrix.toQuadraticForm' G)) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) =
      glLinEquiv K (k : GL (Fin 4) K) := rfl
  rw [this, hk, glLinEquiv_neg_one]


section Minus

theorem toMatrix'_toQuadraticForm' [Invertible (2 : K)] (G : Matrix (Fin 4) (Fin 4) K)
    (hG : Gᵀ = G) : (Matrix.toQuadraticForm' G).toMatrix' = G := by
  have hsymm : ∀ x y : Fin 4 → K, (Matrix.toLinearMap₂' K G) x y = (Matrix.toLinearMap₂' K G) y x := by
    intro x y
    simp only [Matrix.toLinearMap₂'_apply']
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG, dotProduct_comm]
  have h1 : QuadraticMap.associatedHom K (Matrix.toQuadraticForm' G) = Matrix.toLinearMap₂' K G :=
    QuadraticMap.associated_left_inverse (S := K) hsymm
  rw [QuadraticForm.toMatrix', h1]
  exact LinearEquiv.apply_symm_apply (LinearMap.toMatrix₂' K) G


theorem discr'_toQuadraticForm' [Invertible (2 : K)] (G : Matrix (Fin 4) (Fin 4) K) (hG : Gᵀ = G) :
    (Matrix.toQuadraticForm' G).discr' = G.det := by
  rw [QuadraticForm.discr', toMatrix'_toQuadraticForm' G hG]

theorem dot_mulVec_symm (G : Matrix (Fin 4) (Fin 4) K) (hG : Gᵀ = G) (x y : Fin 4 → K) :
    y ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ (G *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG, dotProduct_comm]

theorem polar_toQuadraticForm'_nondeg (h2 : (2 : K) ≠ 0) (G : Matrix (Fin 4) (Fin 4) K)
    (hG : Gᵀ = G) (hdet : G.det ≠ 0) :
    LinearMap.Nondegenerate (polarBilin (Matrix.toQuadraticForm' G)) := by
  have h : polarBilin (Matrix.toQuadraticForm' G) = Matrix.toLinearMap₂' K ((2 : K) • G) := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [Matrix.toQuadraticForm', LinearMap.BilinMap.polarBilin_toQuadraticMap]
    simp only [LinearMap.add_apply, LinearMap.flip_apply, Matrix.toLinearMap₂'_apply',
      Matrix.smul_mulVec, dotProduct_smul, dot_mulVec_symm G hG x y]
    simp only [smul_eq_mul]
    ring
  rw [h]
  apply LinearMap.nondegenerate_toLinearMap₂'_of_det_ne_zero'
  rw [Matrix.det_smul]
  simp [hdet, h2]


@[expose] noncomputable def hypGram (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 2⁻¹, 0; 0, 0, 0, 2⁻¹; 2⁻¹, 0, 0, 0; 0, 2⁻¹, 0, 0]

theorem hypGram_symm : (hypGram K)ᵀ = hypGram K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypGram]

theorem det_hypGram : (hypGram K).det = (2⁻¹ * 2⁻¹) * (2⁻¹ * 2⁻¹) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [hypGram, Matrix.det_fin_three, Fin.succAbove]
  ring

theorem quad_hypGram (v : Fin 4 → K) :
    v ⬝ᵥ (hypGram K *ᵥ v) = 2⁻¹ * (v 0 * v 2 + v 2 * v 0 + (v 1 * v 3 + v 3 * v 1)) := by
  simp [dotProduct, Matrix.mulVec, hypGram, Fin.sum_univ_four]
  ring


theorem isPlusType_hypGram (K : Type) [Field K] :
    CFSG.GroupTheory.WeirSylow.IsPlusType (Matrix.toQuadraticForm' (hypGram K)) := by
  let f : Fin 2 → Fin 4 := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  let b : Fin 2 → (Fin 4 → K) := (⇑(Pi.basisFun K (Fin 4))) ∘ f
  have hb : LinearIndependent K b := (Pi.basisFun K (Fin 4)).linearIndependent.comp f hf
  refine ⟨Submodule.span K (Set.range b), ?_, ?_⟩
  · rw [finrank_span_eq_card hb, Fintype.card_fin, Module.finrank_fin_fun]
  · intro v hv
    have hv' : v 2 = 0 ∧ v 3 = 0 := by
      refine Submodule.span_induction (p := fun w _ => w 2 = 0 ∧ w 3 = 0) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨i, rfl⟩
        fin_cases i <;> simp [b, f, Fin.castLE]
      · simp
      · rintro x y _ _ ⟨hx2, hx3⟩ ⟨hy2, hy3⟩
        simp [hx2, hx3, hy2, hy3]
      · rintro a x _ ⟨hx2, hx3⟩
        simp [hx2, hx3]
    rw [toQuadraticForm'_apply, quad_hypGram, hv'.1, hv'.2]
    simp


theorem toQuadraticForm_minus_of_det_nonsquare [Finite K] (h2 : (2 : K) ≠ 0)
    (G : Matrix (Fin 4) (Fin 4) K) (hsymm : Gᵀ = G) (hdet : ¬ IsSquare G.det) :
    LinearMap.Nondegenerate (polarBilin (Matrix.toQuadraticForm' G)) ∧
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Matrix.toQuadraticForm' G) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hdet0 : G.det ≠ 0 := fun h => hdet ⟨0, by rw [h]; simp⟩
  have hnd := polar_toQuadraticForm'_nondeg h2 G hsymm hdet0
  refine ⟨hnd, fun hp => hdet ?_⟩
  have hH0 : (hypGram K).det ≠ 0 := by
    rw [det_hypGram]
    simp [h2]
  have hndH := polar_toQuadraticForm'_nondeg h2 (hypGram K) hypGram_symm hH0
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff hnd hndH (n := 2)
    (by simp) (by simp) ⟨fun _ => isPlusType_hypGram K, fun _ => hp⟩
  have hcomp : Matrix.toQuadraticForm' G =
      (Matrix.toQuadraticForm' (hypGram K)).comp e.toLinearEquiv.toLinearMap := by
    ext v
    exact (e.map_app v).symm
  have key := QuadraticForm.discr'_comp (Q := Matrix.toQuadraticForm' (hypGram K))
    e.toLinearEquiv.toLinearMap
  rw [← hcomp, discr'_toQuadraticForm' G hsymm, discr'_toQuadraticForm' _ hypGram_symm,
    det_hypGram] at key
  exact ⟨(LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det * (2⁻¹ * 2⁻¹), by rw [key]; ring⟩

end Minus


end CFSG.GH74.Generic.S1.Exo
