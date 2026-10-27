module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup CFSG.ComponentClassification

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def coordImage (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) where
  carrier := {v | (fun i => σ.symm (v i)) ∈ W}
  add_mem' {v w} hv hw := by
    change (fun i => σ.symm ((v + w) i)) ∈ W
    convert W.add_mem hv hw using 1
    ext i
    simp
  zero_mem' := by
    change (fun i => σ.symm ((0 : Fin n → K) i)) ∈ W
    convert W.zero_mem using 1
    ext i
    simp
  smul_mem' c v hv := by
    change (fun i => σ.symm ((c • v) i)) ∈ W
    convert W.smul_mem (σ.symm c) hv using 1
    ext i
    simp

theorem mem_coordImage {σ : K ≃+* K} {W : Submodule K (Fin n → K)} {v : Fin n → K} :
    v ∈ coordImage σ W ↔ (fun i => σ.symm (v i)) ∈ W :=
  Iff.rfl

theorem coord_mem_coordImage {σ : K ≃+* K} {W : Submodule K (Fin n → K)} {w : Fin n → K}
    (hw : w ∈ W) : (fun i => σ (w i)) ∈ coordImage σ W := by
  rw [mem_coordImage]
  simpa using hw

theorem coordImage_injective (σ : K ≃+* K) :
    Function.Injective (coordImage (n := n) σ) := by
  intro W₁ W₂ h
  ext w
  constructor
  · intro hw
    have := coord_mem_coordImage (σ := σ) hw
    rw [h, mem_coordImage] at this
    simpa using this
  · intro hw
    have := coord_mem_coordImage (σ := σ) hw
    rw [← h, mem_coordImage] at this
    simpa using this

theorem coordImage_map (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) :
    coordImage σ (W.map (mulVecLin M)) =
      (coordImage σ W).map (mulVecLin (M.map σ)) := by
  ext v
  rw [mem_coordImage, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    refine ⟨fun i => σ (w i), coord_mem_coordImage hw, ?_⟩
    ext i
    have h := RingHom.map_mulVec σ.toRingHom M w i
    have hw' : (M *ᵥ w) i = σ.symm (v i) := congrFun hwv i
    rw [hw'] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at h
    rw [mulVecLin_apply]
    exact h.symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => σ.symm (u i), mem_coordImage.mp hu, ?_⟩
    ext i
    rw [mulVecLin_apply, mulVecLin_apply]
    have h := RingHom.map_mulVec σ.symm.toRingHom (M.map σ) u i
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
    rw [h]
    congr 2
    ext a b
    simp

@[expose] def dotOrth (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  (1 : Matrix (Fin n) (Fin n) K).toBilin'.orthogonal W

theorem mem_dotOrth {W : Submodule K (Fin n → K)} {v : Fin n → K} :
    v ∈ dotOrth W ↔ ∀ w ∈ W, v ⬝ᵥ w = 0 := by
  rw [dotOrth, LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun w _ => ?_
  rw [toBilin'_apply', one_mulVec, dotProduct_comm]

theorem dotForm_nondegenerate :
    (1 : Matrix (Fin n) (Fin n) K).toBilin'.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _
    (by rw [det_one]; exact one_ne_zero)

theorem dotForm_isRefl : (1 : Matrix (Fin n) (Fin n) K).toBilin'.IsRefl := by
  intro v w h
  rw [toBilin'_apply', one_mulVec] at h ⊢
  rw [dotProduct_comm]
  exact h

theorem finrank_dotOrth (W : Submodule K (Fin n → K)) :
    finrank K (dotOrth W) = n - finrank K W := by
  rw [dotOrth, LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate, finrank_fin_fun]

theorem dotOrth_dotOrth (W : Submodule K (Fin n → K)) : dotOrth (dotOrth W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl W

theorem dotOrth_injective : Function.Injective (dotOrth (K := K) (n := n)) := fun W₁ W₂ h => by
  rw [← dotOrth_dotOrth W₁, h, dotOrth_dotOrth]

theorem map_dotOrth (g : SpecialLinearGroup (Fin n) K) (W : Submodule K (Fin n → K)) :
    (dotOrth W).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) =
      dotOrth (W.map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ)) := by
  have hinv : (g : Matrix (Fin n) (Fin n) K)ᵀ *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    have h : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [← transpose_mul, h, transpose_one]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_dotOrth] at hv
    rw [mem_dotOrth]
    rintro _ ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
      mulVec_mulVec, hinv, one_mulVec, dotProduct_comm]
    exact hv w hw
  · have h1 : finrank K ((dotOrth W).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) =
        finrank K (dotOrth W) := LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _
    have h2 : finrank K (W.map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ)) = finrank K W :=
      LinearEquiv.finrank_map_eq
        (SpecialLinearGroup.toLin' (CatalogueBGraphForm.slGraphAut n K g)) W
    rw [h1, finrank_dotOrth, finrank_dotOrth, h2]

theorem map_mulVecLin_mul (M N : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) :
    W.map (mulVecLin (M * N)) = (W.map (mulVecLin N)).map (mulVecLin M) := by
  rw [mulVecLin_mul, Submodule.map_comp]

theorem map_stabilizer_slConjugation (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    (stabilizer W).map (CatalogueBHigherLinearAction.slConjugation n K A :
        SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K) =
      stabilizer (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) := by
  have hAA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAA' : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext g
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, mem_stabilizer, mem_stabilizer]
  change W.map (mulVecLin ((CatalogueBHigherLinearAction.slConjugation n K A)⁻¹ g :
    SpecialLinearGroup (Fin n) K)) = W ↔ _
  rw [← map_inv, coe_slConjugation, inv_inv, map_mulVecLin_mul, map_mulVecLin_mul]
  have hinvmap : ∀ X : Submodule K (Fin n → K),
      (X.map (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).map
        (mulVecLin (A : Matrix (Fin n) (Fin n) K)) = X := fun X => by
    rw [← Submodule.map_comp, ← mulVecLin_mul, hAA', mulVecLin_one, Submodule.map_id]
  have hmapinv : ∀ X : Submodule K (Fin n → K),
      (X.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))).map
        (mulVecLin ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = X := fun X => by
    rw [← Submodule.map_comp, ← mulVecLin_mul, hAA, mulVecLin_one, Submodule.map_id]
  constructor
  · intro h
    rw [← hinvmap ((W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))).map
      (mulVecLin (g : Matrix (Fin n) (Fin n) K))), h]
  · intro h
    rw [h, hmapinv]

theorem map_stabilizer_slFieldAut (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    (stabilizer W).map (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ :
        SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K) =
      stabilizer (coordImage σ W) := by
  ext g
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, mem_stabilizer, mem_stabilizer]
  change W.map (mulVecLin ((CatalogueBHigherLinearField.slFieldAut (Fin n) K σ)⁻¹ g :
    SpecialLinearGroup (Fin n) K)) = W ↔ _
  rw [← map_inv, ← (coordImage_injective σ).eq_iff, coordImage_map]
  have hmat : (((CatalogueBHigherLinearField.slFieldAut (Fin n) K σ⁻¹) g :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      (g : Matrix (Fin n) (Fin n) K) := by
    ext i j
    change σ (σ.symm _) = _
    exact σ.apply_symm_apply _
  rw [hmat]

theorem map_stabilizer_slGraphAut (W : Submodule K (Fin n → K)) :
    (stabilizer W).map (CatalogueBGraphForm.slGraphAut n K :
        SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K) =
      stabilizer (dotOrth W) := by
  have hinv : (CatalogueBGraphForm.slGraphAut n K).symm = CatalogueBGraphForm.slGraphAut n K := by
    have h := CatalogueBGraphForm.slGraphAut_sq n K
    rw [pow_two] at h
    exact (eq_inv_of_mul_eq_one_left h).symm
  ext g
  rw [Subgroup.map_equiv_eq_comap_symm, hinv, Subgroup.mem_comap, mem_stabilizer, mem_stabilizer]
  rw [map_dotOrth, dotOrth_injective.eq_iff]
  rfl

theorem map_projStabilizer_descendAut (e : MulAut (SpecialLinearGroup (Fin n) K))
    (W : Submodule K (Fin n → K)) :
    (projStabilizer W).map (descendAut n K e : projectiveSL n K →* projectiveSL n K) =
      ((stabilizer W).map (e : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K)).map
        (proj n K) := by
  rw [projStabilizer, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem slField_mul_slConjugation_mul_inv (σ : K ≃+* K) (A : GL (Fin n) K) :
    CatalogueBHigherLinearField.slFieldAut (Fin n) K σ *
        CatalogueBHigherLinearAction.slConjugation n K A *
        (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ)⁻¹ =
      CatalogueBHigherLinearAction.slConjugation n K
        (CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ A) := by
  rw [← map_inv]
  ext g : 1
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ
    (CatalogueBHigherLinearAction.slConjugation n K A
      (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ⁻¹ g))) = _
  rw [CatalogueBHigherLinearField.toGL_slFieldEquiv,
    CatalogueBHigherLinearAction.toGL_slConjugation, CatalogueBHigherLinearField.toGL_slFieldEquiv,
    CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]
  congr 2
  ext i j
  change σ (σ.symm _) = _
  exact σ.apply_symm_apply _

theorem slGraph_mul_slGraph : CatalogueBGraphForm.slGraphAut n K *
    CatalogueBGraphForm.slGraphAut n K = 1 := by
  rw [← pow_two, CatalogueBGraphForm.slGraphAut_sq]

theorem slGraph_mul_slConjugation_mul_slGraph (A : GL (Fin n) K) :
    CatalogueBGraphForm.slGraphAut n K * CatalogueBHigherLinearAction.slConjugation n K A *
        CatalogueBGraphForm.slGraphAut n K =
      CatalogueBHigherLinearAction.slConjugation n K (GeneralLinearGroup.inverseTranspose A) := by
  ext g : 1
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL (CatalogueBGraphForm.slGraphAut n K
    (CatalogueBHigherLinearAction.slConjugation n K A (CatalogueBGraphForm.slGraphAut n K g))) = _
  rw [CatalogueBGraphForm.toGL_slGraphAut, CatalogueBHigherLinearAction.toGL_slConjugation,
    CatalogueBGraphForm.toGL_slGraphAut, CatalogueBHigherLinearAction.toGL_slConjugation,
    map_mul, map_mul, map_inv]
  congr 2
  exact GeneralLinearGroup.inverseTranspose_inverseTranspose _

theorem glFieldEquiv_inverseTranspose (σ : K ≃+* K) (Y : GL (Fin n) K) :
    CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ (GeneralLinearGroup.inverseTranspose Y) =
      GeneralLinearGroup.inverseTranspose
        (CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ Y) := by
  ext i j
  rw [CatalogueBHigherLinearField.glFieldEquiv_entry, GeneralLinearGroup.coe_inverseTranspose,
    GeneralLinearGroup.coe_inverseTranspose, transpose_apply, transpose_apply, ← map_inv,
    CatalogueBHigherLinearField.glFieldEquiv_entry]

theorem slGraph_mul_slField_mul_slGraph (σ : K ≃+* K) :
    CatalogueBGraphForm.slGraphAut n K * CatalogueBHigherLinearField.slFieldAut (Fin n) K σ *
        CatalogueBGraphForm.slGraphAut n K =
      CatalogueBHigherLinearField.slFieldAut (Fin n) K σ := by
  ext g : 1
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL (CatalogueBGraphForm.slGraphAut n K
    (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ (CatalogueBGraphForm.slGraphAut n K g))) =
    SpecialLinearGroup.toGL (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ g)
  rw [CatalogueBGraphForm.toGL_slGraphAut, CatalogueBHigherLinearField.toGL_slFieldEquiv,
    CatalogueBGraphForm.toGL_slGraphAut, CatalogueBHigherLinearField.toGL_slFieldEquiv]
  change GeneralLinearGroup.inverseTranspose (CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ
    (GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL g))) = _
  rw [glFieldEquiv_inverseTranspose, GeneralLinearGroup.inverseTranspose_inverseTranspose]

theorem standard_automorphism_transport :
    (∀ A B : GL (Fin n) K, conjAut n K A * conjAut n K B = conjAut n K (A * B)) ∧
    (∀ σ τ : K ≃+* K, fieldAut n K σ * fieldAut n K τ = fieldAut n K (σ * τ)) ∧
    (∀ (σ : K ≃+* K) (A : GL (Fin n) K), fieldAut n K σ * conjAut n K A * (fieldAut n K σ)⁻¹ =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A)) ∧
    dualAut n K * dualAut n K = 1 ∧
    (∀ A : GL (Fin n) K, dualAut n K * conjAut n K A * dualAut n K =
      conjAut n K (GeneralLinearGroup.inverseTranspose A)) ∧
    (∀ σ : K ≃+* K, dualAut n K * fieldAut n K σ * dualAut n K = fieldAut n K σ) ∧
    (∀ (A : GL (Fin n) K) (W : Submodule K (Fin n → K)),
      (projStabilizer W).map (conjAut n K A : projectiveSL n K →* projectiveSL n K) =
        projStabilizer (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K)))) ∧
    (∀ (σ : K ≃+* K) (W : Submodule K (Fin n → K)),
      (projStabilizer W).map (fieldAut n K σ : projectiveSL n K →* projectiveSL n K) =
        projStabilizer (coordImage σ W)) ∧
    (∀ W : Submodule K (Fin n → K),
      (projStabilizer W).map (dualAut n K : projectiveSL n K →* projectiveSL n K) =
        projStabilizer (dotOrth W)) ∧
    (1 ≤ n →
      (fun L => (projStabilizer L).map (dualAut n K : projectiveSL n K →* projectiveSL n K)) ''
          {L : Submodule K (Fin n → K) | finrank K L = 1} =
        projStabilizer '' {H : Submodule K (Fin n → K) | finrank K H = n - 1} ∧
      (fun H => (projStabilizer H).map (dualAut n K : projectiveSL n K →* projectiveSL n K)) ''
          {H : Submodule K (Fin n → K) | finrank K H = n - 1} =
        projStabilizer '' {L : Submodule K (Fin n → K) | finrank K L = 1}) := by
  have hδ : ∀ W : Submodule K (Fin n → K),
      (projStabilizer W).map (dualAut n K : projectiveSL n K →* projectiveSL n K) =
        projStabilizer (dotOrth W) := fun W => by
    rw [dualAut, map_projStabilizer_descendAut, map_stabilizer_slGraphAut]
    rfl
  refine ⟨fun A B => (map_mul _ A B).symm, fun σ τ => (map_mul _ σ τ).symm, fun σ A => ?_, ?_,
    fun A => ?_, fun σ => ?_, fun A W => ?_, fun σ W => ?_, hδ, fun hn => ⟨?_, ?_⟩⟩
  · change descendAut n K _ * descendAut n K _ * (descendAut n K _)⁻¹ = descendAut n K _
    rw [← map_inv, ← map_mul, ← map_mul, slField_mul_slConjugation_mul_inv]
    rfl
  · rw [dualAut, ← map_mul, slGraph_mul_slGraph, map_one]
  · change descendAut n K _ * descendAut n K _ * descendAut n K _ = descendAut n K _
    rw [← map_mul, ← map_mul, slGraph_mul_slConjugation_mul_slGraph]
  · change descendAut n K _ * descendAut n K _ * descendAut n K _ = descendAut n K _
    rw [← map_mul, ← map_mul, slGraph_mul_slField_mul_slGraph]
  · change (projStabilizer W).map (descendAut n K _ : projectiveSL n K →* projectiveSL n K) = _
    rw [map_projStabilizer_descendAut, map_stabilizer_slConjugation]
    rfl
  · change (projStabilizer W).map (descendAut n K _ : projectiveSL n K →* projectiveSL n K) = _
    rw [map_projStabilizer_descendAut, map_stabilizer_slFieldAut]
    rfl
  · ext M
    constructor
    · rintro ⟨L, hL, rfl⟩
      refine ⟨dotOrth L, ?_, (hδ L).symm⟩
      change finrank K (dotOrth L) = n - 1
      rw [finrank_dotOrth, show finrank K L = 1 from hL]
    · rintro ⟨H, hH, rfl⟩
      refine ⟨dotOrth H, ?_, ?_⟩
      · change finrank K (dotOrth H) = 1
        rw [finrank_dotOrth, show finrank K H = n - 1 from hH]
        omega
      · change (projStabilizer (dotOrth H)).map _ = _
        rw [hδ, dotOrth_dotOrth]
  · ext M
    constructor
    · rintro ⟨H, hH, rfl⟩
      refine ⟨dotOrth H, ?_, (hδ H).symm⟩
      change finrank K (dotOrth H) = 1
      rw [finrank_dotOrth, show finrank K H = n - 1 from hH]
      omega
    · rintro ⟨L, hL, rfl⟩
      refine ⟨dotOrth L, ?_, ?_⟩
      · change finrank K (dotOrth L) = n - 1
        rw [finrank_dotOrth, show finrank K L = 1 from hL]
      · change (projStabilizer (dotOrth L)).map _ = _
        rw [hδ, dotOrth_dotOrth]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
