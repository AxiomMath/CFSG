module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

variable {r : ℕ} {K : Type} [Field K]

theorem pairedSympForm_mulVec_of_formJ {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (hA : Aᵀ * formJ r K * A = μ • formJ r K) (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (A *ᵥ u) (A *ᵥ v) = μ * pairedSympForm K r u v := by
  simp only [pairedSympForm, toBilin'_apply']
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, hA,
    ← dotProduct_mulVec, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem pairedSympForm_map (σ : K ≃+* K) (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (fun i => σ (u i)) (fun i => σ (v i)) = σ (pairedSympForm K r u v) := by
  simp [pairedSympForm_apply, dotProduct, map_sub, map_sum, map_mul]

theorem glFieldEquiv_mem_gsp (σ : K ≃+* K) {A : GL (Fin r ⊕ Fin r) K} (hA : A ∈ gsp r K) :
    glFieldEquiv (Fin r ⊕ Fin r) σ A ∈ gsp r K := by
  obtain ⟨μ, hμ⟩ := hA
  refine ⟨Units.map σ.toRingHom.toMonoidHom μ, ?_⟩
  change ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ)ᵀ * formJ r K *
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ = σ (μ : K) • formJ r K
  have h1 : ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A).map σ =
      ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ)ᵀ * formJ r K *
        (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ := by
    rw [map_mul_ringEquiv, map_mul_ringEquiv, transpose_map, formJ_map]
  rw [← h1, hμ]
  ext i j
  have h := congrFun (congrFun (formJ_map (r := r) σ) i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h ⊢
  rw [h]

@[expose] def gspFieldMap (σ : K ≃+* K) (A : gsp r K) : gsp r K :=
  ⟨glFieldEquiv (Fin r ⊕ Fin r) σ A, glFieldEquiv_mem_gsp σ A.2⟩

theorem coe_gspFieldMap (σ : K ≃+* K) (A : gsp r K) :
    ((gspFieldMap σ A : gsp r K) : GL (Fin r ⊕ Fin r) K) = glFieldEquiv (Fin r ⊕ Fin r) σ A :=
  rfl

@[expose] def spCoordImage (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    Submodule K (Fin r ⊕ Fin r → K) where
  carrier := {v | (fun i => σ.symm (v i)) ∈ W}
  add_mem' {v w} hv hw := by
    change (fun i => σ.symm ((v + w) i)) ∈ W
    convert W.add_mem hv hw using 1
    ext i
    simp
  zero_mem' := by
    change (fun i => σ.symm ((0 : Fin r ⊕ Fin r → K) i)) ∈ W
    convert W.zero_mem using 1
    ext i
    simp
  smul_mem' c v hv := by
    change (fun i => σ.symm ((c • v) i)) ∈ W
    convert W.smul_mem (σ.symm c) hv using 1
    ext i
    simp

theorem mem_spCoordImage {σ : K ≃+* K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {v : Fin r ⊕ Fin r → K} : v ∈ spCoordImage σ W ↔ (fun i => σ.symm (v i)) ∈ W :=
  Iff.rfl

theorem coord_mem_spCoordImage {σ : K ≃+* K} {W : Submodule K (Fin r ⊕ Fin r → K)}
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) : (fun i => σ (w i)) ∈ spCoordImage σ W := by
  rw [mem_spCoordImage]
  simpa using hw

theorem spCoordImage_symm (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    spCoordImage σ.symm (spCoordImage σ W) = W := by
  ext v
  rw [mem_spCoordImage, mem_spCoordImage]
  simp

theorem spCoordImage_map (σ : K ≃+* K) (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (W : Submodule K (Fin r ⊕ Fin r → K)) :
    spCoordImage σ (W.map (mulVecLin M)) = (spCoordImage σ W).map (mulVecLin (M.map σ)) := by
  ext v
  rw [mem_spCoordImage, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    refine ⟨fun i => σ (w i), coord_mem_spCoordImage hw, ?_⟩
    ext i
    have h := RingHom.map_mulVec σ.toRingHom M w i
    have hw' : (M *ᵥ w) i = σ.symm (v i) := congrFun hwv i
    rw [hw'] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at h
    rw [mulVecLin_apply]
    exact h.symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => σ.symm (u i), mem_spCoordImage.mp hu, ?_⟩
    ext i
    rw [mulVecLin_apply, mulVecLin_apply]
    have h := RingHom.map_mulVec σ.symm.toRingHom (M.map σ) u i
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
    rw [h]
    congr 2
    ext a b
    simp

theorem isTotallyIsotropic_spCoordImage (σ : K ≃+* K) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    IsTotallyIsotropic (pairedSympForm K r) (spCoordImage σ W) := by
  intro x hx y hy
  have h := pairedSympForm_map σ (fun i => σ.symm (x i)) (fun i => σ.symm (y i))
  simp only [RingEquiv.apply_symm_apply] at h
  rw [show (fun i => x i) = x from rfl, show (fun i => y i) = y from rfl] at h
  rw [h, hW _ hx _ hy, map_zero]

theorem isTotallyIsotropic_map_gsp (A : gsp r K) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    IsTotallyIsotropic (pairedSympForm K r)
      (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) :=
    by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec_of_formJ hμ, hW x hx y hy, mul_zero]

theorem map_map_mulVecLin_inv (A : GL (Fin r ⊕ Fin r) K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (W.map (mulVecLin (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))).map
      (mulVecLin ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = W :=
    by
  rw [← Submodule.map_comp, ← mulVecLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    mulVecLin_one, Submodule.map_id]

theorem map_stabilizer_conjSp_le (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (stabilizer r K W).map (conjSp r K A).toMonoidHom ≤
      stabilizer r K (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, mem_stabilizer] at hg
  rw [mem_stabilizer]
  change (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))).map (mulVecLin (((A : GL (Fin r ⊕ Fin r) K) *
      (g : GL (Fin r ⊕ Fin r) K) * (A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = _
  rw [← Submodule.map_comp, ← mulVecLin_mul, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul,
    mulVecLin_mul, Submodule.map_comp, hg]

theorem map_stabilizer_conjSp (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (stabilizer r K W).map (conjSp r K A).toMonoidHom =
      stabilizer r K (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) := by
  refine le_antisymm (map_stabilizer_conjSp_le A W) fun h hh => ⟨conjSp r K A⁻¹ h, ?_, ?_⟩
  · have := map_stabilizer_conjSp_le A⁻¹ _ ⟨h, hh, rfl⟩
    rwa [Subgroup.coe_inv, map_map_mulVecLin_inv] at this
  · change conjSp r K A (conjSp r K A⁻¹ h) = h
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem map_stabilizer_fieldSp_le (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (stabilizer r K W).map (fieldSp r K σ).toMonoidHom ≤ stabilizer r K (spCoordImage σ W) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, mem_stabilizer] at hg
  rw [mem_stabilizer]
  change (spCoordImage σ W).map (mulVecLin (((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ)) = _
  rw [← spCoordImage_map, hg]

theorem map_stabilizer_fieldSp (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (stabilizer r K W).map (fieldSp r K σ).toMonoidHom = stabilizer r K (spCoordImage σ W) := by
  refine le_antisymm (map_stabilizer_fieldSp_le σ W) fun h hh => ⟨fieldSp r K σ⁻¹ h, ?_, ?_⟩
  · have := map_stabilizer_fieldSp_le σ⁻¹ _ ⟨h, hh, rfl⟩
    rwa [show σ⁻¹ = σ.symm from rfl, spCoordImage_symm] at this
  · change fieldSp r K σ (fieldSp r K σ⁻¹ h) = h
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem map_projStabilizer_conjAut (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (projStabilizer r K W).map (conjAut r K A).toMonoidHom =
      projStabilizer r K (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) := by
  rw [projStabilizer, projStabilizer, Subgroup.map_map, ← map_stabilizer_conjSp, Subgroup.map_map]
  rfl

theorem map_projStabilizer_fieldAut (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (projStabilizer r K W).map (fieldAut r K σ).toMonoidHom =
      projStabilizer r K (spCoordImage σ W) := by
  rw [projStabilizer, projStabilizer, Subgroup.map_map, ← map_stabilizer_fieldSp, Subgroup.map_map]
  rfl

theorem fieldAut_mul_conjAut_mul_inv (σ : K ≃+* K) (A : gsp r K) :
    fieldAut r K σ * conjAut r K A * (fieldAut r K σ)⁻¹ = conjAut r K (gspFieldMap σ A) := by
  rw [← map_inv]
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  change proj r K (fieldSp r K σ (conjSp r K A (fieldSp r K σ⁻¹ g))) =
    proj r K (conjSp r K (gspFieldMap σ A) g)
  congr 1
  apply Subtype.ext
  change glFieldEquiv (Fin r ⊕ Fin r) σ ((A : GL (Fin r ⊕ Fin r) K) *
      glFieldEquiv (Fin r ⊕ Fin r) σ⁻¹ g * (A : GL (Fin r ⊕ Fin r) K)⁻¹) =
    glFieldEquiv (Fin r ⊕ Fin r) σ A * g * (glFieldEquiv (Fin r ⊕ Fin r) σ A)⁻¹
  rw [map_mul, map_mul, map_inv]
  congr 2
  ext i j
  change σ (σ.symm _) = _
  exact σ.apply_symm_apply _

theorem standard_automorphism_transport :
    (∀ A B : gsp r K, conjAut r K A * conjAut r K B = conjAut r K (A * B)) ∧
    (∀ σ τ : K ≃+* K, fieldAut r K σ * fieldAut r K τ = fieldAut r K (τ.trans σ)) ∧
    (∀ (σ : K ≃+* K) (A : gsp r K),
      fieldAut r K σ * conjAut r K A * (fieldAut r K σ)⁻¹ = conjAut r K (gspFieldMap σ A)) ∧
    (∀ (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)),
      IsTotallyIsotropic (pairedSympForm K r) W →
      IsTotallyIsotropic (pairedSympForm K r) (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)))) ∧
    (∀ (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)),
      IsTotallyIsotropic (pairedSympForm K r) W →
      IsTotallyIsotropic (pairedSympForm K r) (spCoordImage σ W)) ∧
    (∀ (A : gsp r K) (W : Submodule K (Fin r ⊕ Fin r → K)),
      (projStabilizer r K W).map (conjAut r K A).toMonoidHom =
        projStabilizer r K (W.map (mulVecLin ((A : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)))) ∧
    (∀ (σ : K ≃+* K) (W : Submodule K (Fin r ⊕ Fin r → K)),
      (projStabilizer r K W).map (fieldAut r K σ).toMonoidHom =
        projStabilizer r K (spCoordImage σ W)) :=
  ⟨fun A B => (map_mul _ A B).symm, fun σ τ => (map_mul _ σ τ).symm,
    fieldAut_mul_conjAut_mul_inv, fun A _ hW => isTotallyIsotropic_map_gsp A hW,
    fun σ _ hW => isTotallyIsotropic_spCoordImage σ hW, map_projStabilizer_conjAut,
    map_projStabilizer_fieldAut⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
