module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherTransport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFormZero
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSuborbit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryRealization

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

variable {r : ℕ} {K : Type} [Field K]

variable (r) in
@[expose] def sumFinEquiv : Fin r ⊕ Fin r ≃ Fin (2 * r) :=
  finSumFinEquiv.trans (finCongr (two_mul r).symm)

variable (r K) in
@[expose] def reindexLinearEquiv : (Fin (2 * r) → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.funCongrLeft K K (sumFinEquiv r)

theorem reindexLinearEquiv_apply (v : Fin (2 * r) → K) (x : Fin r ⊕ Fin r) :
    reindexLinearEquiv r K v x = v (sumFinEquiv r x) :=
  rfl

theorem map_reindex_symm_map (X : Submodule K (Fin (2 * r) → K)) :
    (X.map (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K)).map
      ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K) = X := by
  rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]

theorem map_reindex_map_symm (Y : Submodule K (Fin r ⊕ Fin r → K)) :
    (Y.map ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K)).map
      (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K) = Y := by
  rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]

theorem map_reindex_le_iff {X Y : Submodule K (Fin (2 * r) → K)} :
    X.map (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K) ≤
      Y.map (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K) ↔ X ≤ Y := by
  refine ⟨fun h => ?_, Submodule.map_mono⟩
  have := Submodule.map_mono
    (f := ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K)) h
  rwa [map_reindex_symm_map, map_reindex_symm_map] at this

theorem map_reindex_symm_le_iff {X Y : Submodule K (Fin r ⊕ Fin r → K)} :
    X.map ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K) ≤
      Y.map ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K) ↔
        X ≤ Y := by
  refine ⟨fun h => ?_, Submodule.map_mono⟩
  have := Submodule.map_mono
    (f := (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K)) h
  rwa [map_reindex_map_symm, map_reindex_map_symm] at this

theorem map_reindex_coordImage (σ : K ≃+* K) (X : Submodule K (Fin (2 * r) → K)) :
    (LinearFlag.coordImage σ X).map
        (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K) =
      spCoordImage σ (X.map
        (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K)) := by
  ext v
  rw [Submodule.mem_map_equiv, mem_spCoordImage, Submodule.mem_map_equiv,
    LinearFlag.mem_coordImage]
  rfl

theorem map_reindex_mulVecLin (M : Matrix (Fin (2 * r)) (Fin (2 * r)) K)
    (X : Submodule K (Fin (2 * r) → K)) :
    (X.map (mulVecLin M)).map
        (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K) =
      (X.map (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K)).map
        (mulVecLin (M.submatrix (sumFinEquiv r) (sumFinEquiv r))) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, mulVecLin_apply, mulVecLin_apply,
    submatrix_mulVec_equiv]
  have hv : (reindexLinearEquiv r K v) ∘ (sumFinEquiv r).symm = v := funext fun j => by
    rw [Function.comp_apply, reindexLinearEquiv_apply, Equiv.apply_symm_apply]
  rw [LinearEquiv.coe_coe, hv]
  rfl

@[expose] def reindexGL (A : GL (Fin (2 * r)) K) : GL (Fin r ⊕ Fin r) K :=
  ⟨(A : Matrix (Fin (2 * r)) (Fin (2 * r)) K).submatrix (sumFinEquiv r) (sumFinEquiv r),
    ((A⁻¹ : GL (Fin (2 * r)) K) : Matrix (Fin (2 * r)) (Fin (2 * r)) K).submatrix (sumFinEquiv r)
      (sumFinEquiv r),
    by rw [submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      submatrix_one_equiv],
    by rw [submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      submatrix_one_equiv]⟩

theorem coe_reindexGL (A : GL (Fin (2 * r)) K) :
    ((reindexGL A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (A : Matrix (Fin (2 * r)) (Fin (2 * r)) K).submatrix (sumFinEquiv r) (sumFinEquiv r) :=
  rfl

@[expose] def pointsReindex : ProjectiveGeometry.Point (2 * r) K ≃ SpPoint r K where
  toFun L := ⟨L.1.map (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K),
    ((reindexLinearEquiv r K).finrank_map_eq L.1).trans L.2⟩
  invFun M := ⟨M.line.map
      ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K),
    ((reindexLinearEquiv r K).symm.finrank_map_eq M.line).trans M.finrank_line⟩
  left_inv L := Subtype.ext (map_reindex_symm_map L.1)
  right_inv M := SpPoint.ext (map_reindex_map_symm M.line)

@[expose] def hyperplanesReindex : ProjectiveGeometry.Hyperplane (2 * r) K ≃
    {H : Submodule K (Fin r ⊕ Fin r → K) // finrank K H = 2 * r - 1} where
  toFun H := ⟨H.1.map (reindexLinearEquiv r K : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K),
    ((reindexLinearEquiv r K).finrank_map_eq H.1).trans H.2⟩
  invFun H := ⟨H.1.map
      ((reindexLinearEquiv r K).symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K),
    ((reindexLinearEquiv r K).symm.finrank_map_eq H.1).trans H.2⟩
  left_inv H := Subtype.ext (map_reindex_symm_map H.1)
  right_inv H := Subtype.ext (map_reindex_map_symm H.1)

theorem finrank_orthogonal_of_finrank (hr : 1 ≤ r) {H : Submodule K (Fin r ⊕ Fin r → K)}
    (hH : finrank K H = 2 * r - 1) : finrank K ((pairedSympForm K r).orthogonal H) = 1 := by
  have h := BilinForm.finrank_add_finrank_orthogonal SymplecticFlag.pairedSympForm_isAlt.isRefl H
  rw [BilinForm.orthogonal_top_eq_bot SymplecticFlag.pairedSympForm_nondegenerate, inf_bot_eq,
    finrank_bot, add_zero, finrank_standard, hH] at h
  omega

@[expose] def hyperplanePointEquiv (hr : 1 ≤ r) :
    {H : Submodule K (Fin r ⊕ Fin r → K) // finrank K H = 2 * r - 1} ≃ SpPoint r K where
  toFun H := ⟨(pairedSympForm K r).orthogonal H.1, finrank_orthogonal_of_finrank hr H.2⟩
  invFun M := ⟨(pairedSympForm K r).orthogonal M.line, finrank_orthogonal_line M⟩
  left_inv H := Subtype.ext (BilinForm.orthogonal_orthogonal
    SymplecticFlag.pairedSympForm_nondegenerate SymplecticFlag.pairedSympForm_isAlt.isRefl H.1)
  right_inv M := SpPoint.ext (BilinForm.orthogonal_orthogonal
    SymplecticFlag.pairedSympForm_nondegenerate SymplecticFlag.pairedSympForm_isAlt.isRefl M.line)

theorem transpose_formJ_mul_eq_of_forall {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (h : ∀ u v, pairedSympForm K r (A *ᵥ u) (A *ᵥ v) = μ * pairedSympForm K r u v) :
    Aᵀ * formJ r K * A = μ • formJ r K := by
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp, map_smul]
  refine LinearMap.ext₂ fun u v => ?_
  rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  exact h u v

theorem mulVec_ne_zero_of_ne_zero (A : GL (Fin r ⊕ Fin r) K) {w : Fin r ⊕ Fin r → K}
    (hw : w ≠ 0) : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ≠ 0 := by
  intro h
  apply hw
  have := congrArg (fun z => ((A⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ z) h
  simp only [mulVec_mulVec, mulVec_zero] at this
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at this

theorem coord_ne_zero (σ : K ≃+* K) {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    (fun i => σ (v i)) ≠ 0 := fun h =>
  hv (funext fun i => (map_eq_zero_iff σ σ.injective).mp (congrFun h i))

theorem spCoordImage_span_singleton (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    spCoordImage σ (span K {v}) = span K {fun i => σ (v i)} := by
  ext w
  rw [mem_spCoordImage, mem_span_singleton, mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨σ a, funext fun i => ?_⟩
    have := congrFun ha i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← map_mul, this, RingEquiv.apply_symm_apply]
  · rintro ⟨b, rfl⟩
    refine ⟨σ.symm b, funext fun i => ?_⟩
    simp

theorem geometric_semilinear_realization (hr : 2 ≤ r) (f : SpPoint r K ≃ SpPoint r K)
    (hf : ∀ L M : SpPoint r K, SpOrth L M ↔ SpOrth (f L) (f M)) :
    ∃ (A : GL (Fin r ⊕ Fin r) K) (σ : K ≃+* K) (μ : Kˣ),
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = (μ : K) • formJ r K ∧
      ∀ L : SpPoint r K, (f L).line =
        (spCoordImage σ L.line).map (mulVecLin (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
  classical
  set T := reindexLinearEquiv r K
  set e := hyperplanePointEquiv (K := K) (by omega : 1 ≤ r)
  have hinc : ∀ (L : SpPoint r K)
      (H : {H : Submodule K (Fin r ⊕ Fin r → K) // finrank K H = 2 * r - 1}),
      L.line ≤ H.1 ↔ (f L).line ≤ ((e.trans (f.trans e.symm)) H).1 := by
    intro L H
    have hH : H.1 = (pairedSympForm K r).orthogonal (e H).line :=
      (BilinForm.orthogonal_orthogonal SymplecticFlag.pairedSympForm_nondegenerate
        SymplecticFlag.pairedSympForm_isAlt.isRefl H.1).symm
    have hhS : ((e.trans (f.trans e.symm)) H).1 =
        (pairedSympForm K r).orthogonal (f (e H)).line := rfl
    rw [hhS, ← spOrth_iff_le_orthogonal]
    conv_lhs => rw [hH]
    rw [← spOrth_iff_le_orthogonal]
    exact hf _ _
  have hincN : ∀ (L : ProjectiveGeometry.Point (2 * r) K)
      (H : ProjectiveGeometry.Hyperplane (2 * r) K),
      (L : Submodule K (Fin (2 * r) → K)) ≤ H ↔
        ((pointsReindex.trans (f.trans pointsReindex.symm)) L : Submodule K (Fin (2 * r) → K)) ≤
          (hyperplanesReindex.trans ((e.trans (f.trans e.symm)).trans hyperplanesReindex.symm))
            H := by
    intro L H
    rw [← map_reindex_le_iff]
    exact (hinc (pointsReindex L) (hyperplanesReindex H)).trans map_reindex_symm_le_iff.symm
  obtain ⟨A₀, σ, hA₀, -⟩ := ProjectiveGeometry.semilinear_realization (by omega : 3 ≤ 2 * r)
    (pointsReindex.trans (f.trans pointsReindex.symm))
    (hyperplanesReindex.trans ((e.trans (f.trans e.symm)).trans hyperplanesReindex.symm)) hincN
  set A := reindexGL A₀
  have hfL : ∀ L : SpPoint r K, (f L).line =
      (spCoordImage σ L.line).map (mulVecLin (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
    intro L
    have h1 : (f L).line.map (T.symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K) =
        (LinearFlag.coordImage σ (L.line.map
          (T.symm : (Fin r ⊕ Fin r → K) →ₗ[K] Fin (2 * r) → K))).map
          (mulVecLin (A₀ : Matrix (Fin (2 * r)) (Fin (2 * r)) K)) := by
      have := hA₀ (pointsReindex.symm L)
      rwa [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at this
    have h2 := congrArg (Submodule.map (T : (Fin (2 * r) → K) →ₗ[K] Fin r ⊕ Fin r → K)) h1
    rw [map_reindex_map_symm, map_reindex_mulVecLin, map_reindex_coordImage,
      map_reindex_map_symm] at h2
    rw [h2, coe_reindexGL]
  have hfv : ∀ (v : Fin r ⊕ Fin r → K) (hv : v ≠ 0),
      f (SpPoint.ofVec v hv) = SpPoint.ofVec _ (mulVec_ne_zero_of_ne_zero A (coord_ne_zero σ hv)) :=
    fun v hv => SpPoint.ext (by
      rw [hfL, line_ofVec, spCoordImage_span_singleton, Submodule.map_span, Set.image_singleton,
        line_ofVec, mulVecLin_apply])
  have hzero : ∀ x y : Fin r ⊕ Fin r → K, pairedSympForm K r x y = 0 ↔
      pairedSympForm K r ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x)
        ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y) = 0 := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hu := coord_ne_zero σ.symm hx
    have hv := coord_ne_zero σ.symm hy
    have h1 := hf (SpPoint.ofVec _ hu) (SpPoint.ofVec _ hv)
    rw [spOrth_ofVec_iff, hfv, hfv, spOrth_ofVec_iff] at h1
    have hσx : (fun i => σ (σ.symm (x i))) = x := funext fun i => σ.apply_symm_apply _
    have hσy : (fun i => σ (σ.symm (y i))) = y := funext fun i => σ.apply_symm_apply _
    rw [hσx, hσy, pairedSympForm_map σ.symm x y] at h1
    rw [← h1]
    exact (map_eq_zero_iff σ.symm σ.symm.injective).symm
  obtain ⟨μ, hμ⟩ := form_zero_relation (b := pairedSympForm K r)
    (c := (pairedSympForm K r).compl₁₂
      (mulVecLin (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
      (mulVecLin (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) hzero
  exact ⟨A, σ, μ, transpose_formJ_mul_eq_of_forall fun u v => hμ u v, hfL⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
