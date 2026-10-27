module

public import CFSG.GH74.Generic.S1.UniForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def cT (h : UnitaryFieldData p f F) {m n : Type} (M : Matrix m n F) : Matrix n m F :=
  (M.map h.bar)ᵀ

section cT

variable (h : UnitaryFieldData p f F) {m n o : Type}

theorem cT_def (M : Matrix m n F) : cT h M = (M.map h.bar)ᵀ := rfl

theorem cT_mul [Fintype n] (M : Matrix m n F) (N : Matrix n o F) :
    cT h (M * N) = cT h N * cT h M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (M : Matrix m n F) : cT h (cT h M) = M := by
  ext i j
  simp [cT, h.bar_bar]

theorem cT_one [DecidableEq m] : cT h (1 : Matrix m m F) = 1 := by
  simp [cT, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]

theorem cT_add (M N : Matrix m n F) : cT h (M + N) = cT h M + cT h N := by
  simp [cT, Matrix.map_add _ (map_add h.bar), Matrix.transpose_add]

theorem cT_sub (M N : Matrix m n F) : cT h (M - N) = cT h M - cT h N := by
  ext i j
  simp [cT]

theorem cT_neg (M : Matrix m n F) : cT h (-M) = -cT h M := by
  ext i j
  simp [cT]

theorem cT_smul (c : F) (M : Matrix m n F) : cT h (c • M) = h.bar c • cT h M := by
  ext i j
  simp [cT]

theorem cT_zero : cT h (0 : Matrix m n F) = 0 := by
  ext i j
  simp [cT]

end cT

theorem rank_map_le (σ : F →+* F) {m n : Type} [Fintype m] [Fintype n] (B : Matrix m n F) :
    (B.map σ).rank ≤ B.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  set W : Submodule F (m → F) := Submodule.span F (Set.range B.col) with hW
  let φ : (m → F) →ₛₗ[σ] (m → F) :=
    { toFun := fun v i => σ (v i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }
  let bW := Module.finBasis F W
  let s : Finset (m → F) := Finset.univ.image (fun l => φ (bW l : m → F))
  have hsub : Submodule.span F (Set.range (B.map σ).col) ≤ Submodule.span F (s : Set (m → F)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : B.col j ∈ W := Submodule.subset_span ⟨j, rfl⟩
    have hrepr := bW.sum_repr ⟨B.col j, hj⟩
    have hcol : B.col j = ∑ l, bW.repr ⟨B.col j, hj⟩ l • (bW l : m → F) := by
      have := congrArg (fun x : W => (x : m → F)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    have himg : (B.map σ).col j = φ (B.col j) := by
      ext i; rfl
    rw [himg, hcol, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)))
  calc Module.finrank F (Submodule.span F (Set.range (B.map σ).col))
      ≤ Module.finrank F (Submodule.span F (s : Set (m → F))) := Submodule.finrank_mono hsub
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Module.finrank F W := by simp

theorem rank_cT (h : UnitaryFieldData p f F) {m n : Type} [Fintype m] [Fintype n]
    (M : Matrix m n F) : (cT h M).rank = M.rank := by
  rw [cT, Matrix.rank_transpose]
  refine le_antisymm (rank_map_le _ M) ?_
  have := rank_map_le (h.bar : F →+* F) (M.map h.bar)
  rwa [map_bar_bar] at this

section Paired

variable (h : UnitaryFieldData p f F)

theorem cT_eq_neg_of_sq {Bm : Matrix (Fin 4) (Fin 4) F} (hBB : Bm * Bm = 1)
    (hBu : cT h Bm * Bm = -1) : cT h Bm = -Bm := by
  calc cT h Bm = cT h Bm * (Bm * Bm) := by rw [hBB, Matrix.mul_one]
    _ = (cT h Bm * Bm) * Bm := (Matrix.mul_assoc _ _ _).symm
    _ = -Bm := by rw [hBu]; simp

theorem finrank_eigen_eq_two (hp2 : p ≠ 2) {Bm : Matrix (Fin 4) (Fin 4) F} (hBB : Bm * Bm = 1)
    (hBu : cT h Bm * Bm = -1) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' Bm - 1)) = 2 ∧
      Module.finrank F (LinearMap.ker (Matrix.toLin' Bm + 1)) = 2 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  have hBs := cT_eq_neg_of_sq h hBB hBu
  have hTT : Matrix.toLin' Bm * Matrix.toLin' Bm = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hBB, Matrix.toLin'_one]
    rfl
  have hc := isCompl_ker_sub_one_ker_add_one h2 hTT
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at hsum
  have hT1 : Matrix.toLin' Bm - 1 = Matrix.toLin' (Bm - 1) := by
    rw [map_sub, Matrix.toLin'_one]
    rfl
  have hT2 : Matrix.toLin' Bm + 1 = Matrix.toLin' (Bm + 1) := by
    rw [map_add, Matrix.toLin'_one]
    rfl
  have hr1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (Bm - 1))
  have hr2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (Bm + 1))
  rw [Module.finrank_fin_fun] at hr1 hr2
  have hrank : (Bm + 1).rank = (Bm - 1).rank := by
    have h1 : Bm + 1 = (-1 : F) • cT h (Bm - 1) := by
      rw [cT_sub, cT_one, hBs]
      ext i j
      simp
      ring
    rw [h1, Matrix.rank_smul_of_mem_nonZeroDivisors _ (by simp), rank_cT]
  have e1 : Module.finrank F (LinearMap.range (Matrix.toLin' (Bm - 1))) = (Bm - 1).rank := rfl
  have e2 : Module.finrank F (LinearMap.range (Matrix.toLin' (Bm + 1))) = (Bm + 1).rank := rfl
  rw [hT1, hT2]
  rw [hT1, hT2] at hsum
  omega

theorem eq_zero_of_eq_neg {m n : Type} {M : Matrix m n F} (h2 : (2 : F) ≠ 0) (hM : M = -M) :
    M = 0 := by
  ext i j
  have h1 := congrFun (congrFun hM i) j
  simp only [Matrix.neg_apply] at h1
  have h3 : (2 : F) * M i j = 0 := by linear_combination h1
  simpa [h2] using h3

def colsOf {ι : Type} (v : ι → (Fin 4 → F)) : Matrix (Fin 4) ι F := Matrix.of fun i j => v j i

theorem colsOf_mulVec_apply {ι : Type} [Fintype ι] (v : ι → (Fin 4 → F)) (a : ι → F) :
    colsOf v *ᵥ a = ∑ j, a j • v j := by
  ext i
  simp [colsOf, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem mul_colsOf {ι : Type} (M : Matrix (Fin 4) (Fin 4) F) (v : ι → (Fin 4 → F)) :
    M * colsOf v = colsOf (fun j => M *ᵥ v j) := by
  ext i j
  simp [colsOf, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem cT_mul_colsOf {ι κ : Type} [Fintype ι] (v : ι → (Fin 4 → F)) (w : κ → (Fin 4 → F)) (a : ι) (b : κ) :
    (cT h (colsOf v) * colsOf w) a b = gramForm h (1 : Matrix (Fin 4) (Fin 4) F) (v a) (w b) := by
  simp [cT, colsOf, Matrix.mul_apply, gramForm_apply, dotProduct, Matrix.transpose_apply]

theorem exists_paired_basis (hp2 : p ≠ 2) {Bm : Matrix (Fin 4) (Fin 4) F} (hBB : Bm * Bm = 1)
    (hBu : cT h Bm * Bm = -1) :
    ∃ P : GL (Fin 4) F, cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
        wMat ∧
      Bm * (P : Matrix (Fin 4) (Fin 4) F) =
        (P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (-1) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  have hBs : cT h Bm = -Bm := cT_eq_neg_of_sq h hBB hBu
  obtain ⟨hU2, hW2⟩ := finrank_eigen_eq_two h hp2 hBB hBu
  set T : Module.End F (Fin 4 → F) := Matrix.toLin' Bm with hT
  set U := LinearMap.ker (T - 1) with hUdef
  set W := LinearMap.ker (T + 1) with hWdef
  have hTT : T * T = 1 := by
    rw [hT, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hBB, Matrix.toLin'_one]
    rfl
  have hc : IsCompl U W := isCompl_ker_sub_one_ker_add_one h2 hTT
  set D := gramForm h (1 : Matrix (Fin 4) (Fin 4) F) with hD
  have hDT : ∀ v w, D (T v) (T w) = -D v w := by
    intro v w
    rw [hD, hT]
    simp only [Matrix.toLin'_apply]
    rw [gramForm_mulVec]
    have : (Bm.map h.bar)ᵀ * (1 : Matrix (Fin 4) (Fin 4) F) * Bm = -1 := by
      rw [Matrix.mul_one]; exact hBu
    rw [this]
    simp [gramForm_apply, Matrix.neg_mulVec, dotProduct_neg]
  have hUU : ∀ v ∈ U, ∀ w ∈ U, D v w = 0 := fun v hv w hw =>
    sesq_eq_zero_of_eigen_neg_plus h2 hDT hv hw
  have hWW : ∀ v ∈ W, ∀ w ∈ W, D v w = 0 := fun v hv w hw =>
    sesq_eq_zero_of_eigen_neg_minus h2 hDT hv hw
  let bU : Module.Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hU2
  let bW : Module.Basis (Fin 2) F W := Module.finBasisOfFinrankEq F W hW2
  let Mm : Matrix (Fin 2) (Fin 2) F :=
    Matrix.of fun j k => D (bU j : Fin 4 → F) (bW k : Fin 4 → F)
  have hDsymm : D.IsSymm := gramForm_isSymm h (by simp)
  have hDsep : D.SeparatingLeft := gramForm_separatingLeft h (by simp)
  have hMinj : ∀ c : Fin 2 → F, Mm *ᵥ c = 0 → c = 0 := by
    intro c hc0
    obtain ⟨w, hw⟩ : ∃ w : Fin 4 → F, w = ∑ k, c k • (bW k : Fin 4 → F) := ⟨_, rfl⟩
    have hwW : w ∈ W := by
      rw [hw]
      exact Submodule.sum_mem _ fun k _ => W.smul_mem _ (bW k).2
    have hUw : ∀ j, D (bU j : Fin 4 → F) w = 0 := by
      intro j
      have h1 := congrFun hc0 j
      simp only [Matrix.mulVec, dotProduct, Mm, Matrix.of_apply, Pi.zero_apply] at h1
      rw [hw, map_sum]
      simpa [LinearMap.map_smul, mul_comm] using h1
    have hUw' : ∀ u ∈ U, D u w = 0 := by
      intro u hu
      have hu' : u = ∑ j, bU.repr ⟨u, hu⟩ j • (bU j : Fin 4 → F) := by
        have := congrArg Subtype.val (bU.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [hu', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hUw j, smul_zero]
    have hxw : ∀ x, D x w = 0 := by
      intro x
      obtain ⟨u, w', hu, hw', rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint x
      rw [map_add, LinearMap.add_apply, hUw' u hu, hWW w' hw' w hwW, add_zero]
    have hw0 : w = 0 := hDsep w fun y => by
      rw [← hDsymm.eq y w, hxw y, map_zero]
    have hsum : ∑ k, c k • bW k = 0 := by
      apply Subtype.ext
      simpa [hw] using hw0.symm.symm
    exact funext (Fintype.linearIndependent_iff.1 bW.linearIndependent c hsum)
  have hMunit : IsUnit Mm := by
    refine Matrix.mulVec_injective_iff_isUnit.1 fun a b hab => ?_
    have := hMinj (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
    exact sub_eq_zero.1 this
  have hMdet : IsUnit Mm.det := (Matrix.isUnit_iff_isUnit_det _).1 hMunit
  let E₀ : Matrix (Fin 4) (Fin 2) F := colsOf fun j => (bU j : Fin 4 → F)
  let W₀ : Matrix (Fin 4) (Fin 2) F := colsOf fun j => (bW j : Fin 4 → F)
  have hBE : Bm * E₀ = E₀ := by
    rw [mul_colsOf]
    ext i j
    have h1 : Bm *ᵥ (bU j : Fin 4 → F) = bU j := by
      have := apply_eq_of_mem_ker_sub_one (bU j).2
      simpa [hT, Matrix.toLin'_apply] using this
    exact congrFun h1 i
  have hBW : Bm * W₀ = -W₀ := by
    rw [mul_colsOf]
    ext i j
    have h1 : Bm *ᵥ (bW j : Fin 4 → F) = -(bW j : Fin 4 → F) := by
      have := apply_eq_neg_of_mem_ker_add_one (bW j).2
      simpa [hT, Matrix.toLin'_apply] using this
    exact congrFun h1 i
  have hEE : cT h E₀ * E₀ = 0 := by
    ext a b
    rw [cT_mul_colsOf]
    exact hUU _ (bU a).2 _ (bU b).2
  have hWW0 : cT h W₀ * W₀ = 0 := by
    ext a b
    rw [cT_mul_colsOf]
    exact hWW _ (bW a).2 _ (bW b).2
  have hMeq : cT h E₀ * W₀ = Mm := by
    ext a b
    rw [cT_mul_colsOf]
    rfl
  let W₁ : Matrix (Fin 4) (Fin 2) F := W₀ * Mm⁻¹
  have hMM : Mm * Mm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMdet
  have hEW1 : cT h E₀ * W₁ = 1 := by
    change cT h E₀ * (W₀ * Mm⁻¹) = 1
    rw [← Matrix.mul_assoc, hMeq, hMM]
  have hW1W1 : cT h W₁ * W₁ = 0 := by
    change cT h (W₀ * Mm⁻¹) * (W₀ * Mm⁻¹) = 0
    rw [cT_mul]
    calc cT h Mm⁻¹ * cT h W₀ * (W₀ * Mm⁻¹) = cT h Mm⁻¹ * (cT h W₀ * W₀) * Mm⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hWW0]; simp
  have hW1E : cT h W₁ * E₀ = 1 := by
    have := congrArg (cT h) hEW1
    rwa [cT_mul, cT_cT, cT_one] at this
  have hBW1 : Bm * W₁ = -W₁ := by
    change Bm * (W₀ * Mm⁻¹) = -(W₀ * Mm⁻¹)
    rw [← Matrix.mul_assoc, hBW, Matrix.neg_mul]
  let Pc : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := Matrix.fromCols E₀ W₁
  let Pm : Matrix (Fin 4) (Fin 4) F := Pc.submatrix id e4.symm
  have hgram : cT h Pm * Pm = wMat := by
    have h1 : cT h Pm = (cT h Pc).submatrix e4.symm id := by
      ext i j
      simp [cT, Pm, Matrix.transpose_apply]
    have h2' : cT h Pc = Matrix.fromRows (cT h E₀) (cT h W₁) := by
      simp only [cT, Pc, Matrix.fromCols_map, Matrix.transpose_fromCols]
    have h3 : cT h Pc * Pc = Matrix.fromBlocks 0 1 1 0 := by
      rw [h2', Matrix.fromRows_mul_fromCols, hEE, hEW1, hW1E, hW1W1]
    change (cT h Pm) * (Pc.submatrix id e4.symm) = wMat
    rw [h1, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, h3]
    rw [wMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  have hdet : Pm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgram
    rw [Matrix.det_mul, det_wMat] at this
    have h5 : (cT h Pm).det = h.bar Pm.det := by
      rw [cT, Matrix.det_transpose]
      exact (RingHom.map_det (h.bar : F →+* F) Pm).symm
    rw [h5, h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  let Qd : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) 0 0 (-1)
  have hBc : Bm * Pc = Pc * Qd := by
    simp only [Pc, Qd]
    rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hBE, hBW1]
    simp
  have hBP : Bm * Pm = Pm * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (-1) := by
    have h1 : Bm * Pm = (Bm * Pc).submatrix id e4.symm := rfl
    have h2' : Pm * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (-1) = (Pc * Qd).submatrix id e4.symm := by
      rw [blk4_eq_reindex, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
      exact Matrix.submatrix_mul_equiv Pc Qd id e4.symm e4.symm
    rw [h1, h2', hBc]
  exact ⟨Matrix.GeneralLinearGroup.mk'' Pm (isUnit_iff_ne_zero.2 hdet), hgram, hBP⟩

end Paired

end CFSG.GH74.Generic.S1.Uni
