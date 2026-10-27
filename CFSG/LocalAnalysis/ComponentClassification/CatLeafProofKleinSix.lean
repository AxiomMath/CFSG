module

public import CFSG.LocalAnalysis.SteinbergCEPfaffianFour
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.KleinSix

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis (antiMat pfS)

variable {K : Type} [Field K]

@[expose] def skewOf (v : Fin 3 ⊕ Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  antiMat (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 2)) (-v (.inr 1)) (v (.inr 0))

@[expose] def coordsOf (X : Matrix (Fin 4) (Fin 4) K) : Fin 3 ⊕ Fin 3 → K :=
  Sum.elim ![X 0 1, X 0 2, X 0 3] ![X 2 3, -X 1 3, X 1 2]

theorem coordsOf_skewOf (v : Fin 3 ⊕ Fin 3 → K) : coordsOf (skewOf v) = v := by
  funext k
  rcases k with i | i <;> fin_cases i <;> simp [coordsOf, skewOf, antiMat]

theorem antiMat_transpose (a b c d e f : K) :
    (antiMat a b c d e f)ᵀ = -antiMat a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiMat]

theorem skewOf_coordsOf {Y : Matrix (Fin 4) (Fin 4) K} (hY : Yᵀ = -Y)
    (hd : ∀ i, Y i i = 0) : skewOf (coordsOf Y) = Y := by
  have h : ∀ i j, Y j i = -Y i j := fun i j => by
    have := congrFun (congrFun hY i) j
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordsOf, skewOf, antiMat, hd, h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]

theorem congr_transpose (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    (g * skewOf v * gᵀ)ᵀ = -(g * skewOf v * gᵀ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, skewOf,
    antiMat_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem skewOf_coordsOf_congr (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    skewOf (coordsOf (g * skewOf v * gᵀ)) = g * skewOf v * gᵀ :=
  skewOf_coordsOf (congr_transpose g v) fun i =>
    CFSG.LocalAnalysis.congr_antiMat_apply_self g _ _ _ _ _ _ i

theorem quadPlus_eq_pfS (v : Fin 3 ⊕ Fin 3 → K) : quadPlus 3 K v = pfS (skewOf v) := by
  rw [quadPlus_apply]
  simp [pfS, skewOf, antiMat, Fin.sum_univ_three]

@[expose] def skewLin : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] Matrix (Fin 4) (Fin 4) K where
  toFun := skewOf
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewOf, antiMat] <;> ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewOf, antiMat]

@[expose] def coordsLin : Matrix (Fin 4) (Fin 4) K →ₗ[K] (Fin 3 ⊕ Fin 3 → K) where
  toFun := coordsOf
  map_add' X Y := by
    funext k
    rcases k with i | i <;> fin_cases i <;> simp [coordsOf, add_comm]
  map_smul' c X := by
    funext k
    rcases k with i | i <;> fin_cases i <;> simp [coordsOf]

@[expose] def kleinLin (g : Matrix (Fin 4) (Fin 4) K) :
    (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  coordsLin ∘ₗ ((LinearMap.mulLeft K g) ∘ₗ (LinearMap.mulRight K gᵀ)) ∘ₗ skewLin

theorem kleinLin_apply (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    kleinLin g v = coordsOf (g * skewOf v * gᵀ) := by
  simp [kleinLin, skewLin, coordsLin, Matrix.mul_assoc]

theorem kleinLin_mul (g h : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    kleinLin (g * h) v = kleinLin g (kleinLin h v) := by
  rw [kleinLin_apply, kleinLin_apply, kleinLin_apply, skewOf_coordsOf_congr,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem kleinLin_one (v : Fin 3 ⊕ Fin 3 → K) : kleinLin 1 v = v := by
  rw [kleinLin_apply, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, coordsOf_skewOf]

theorem quadPlus_kleinLin (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 3 K (kleinLin g v) = g.det * quadPlus 3 K v := by
  rw [kleinLin_apply, quadPlus_eq_pfS, skewOf_coordsOf_congr, quadPlus_eq_pfS, skewOf,
    CFSG.LocalAnalysis.pfS_congr]

@[expose] def rhoGL :
    Matrix.SpecialLinearGroup (Fin 4) K →* ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) where
  toFun g := LinearEquiv.ofLinearMap (kleinLin (g : Matrix (Fin 4) (Fin 4) K))
    (kleinLin ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← kleinLin_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, kleinLin_one, LinearMap.id_apply])
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← kleinLin_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, kleinLin_one, LinearMap.id_apply])
  map_one' := LinearEquiv.ext fun v => by
    change kleinLin _ v = v
    rw [Matrix.SpecialLinearGroup.coe_one, kleinLin_one]
  map_mul' g h := LinearEquiv.ext fun v => by
    change kleinLin _ v = kleinLin _ (kleinLin _ v)
    rw [Matrix.SpecialLinearGroup.coe_mul, kleinLin_mul]

theorem rhoGL_apply (g : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    rhoGL g v = coordsOf ((g : Matrix (Fin 4) (Fin 4) K) * skewOf v *
      (g : Matrix (Fin 4) (Fin 4) K)ᵀ) :=
  kleinLin_apply _ v

theorem rhoGL_mem_orthogonalGroup (g : Matrix.SpecialLinearGroup (Fin 4) K) :
    rhoGL g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  change quadPlus 3 K (kleinLin _ v) = _
  rw [quadPlus_kleinLin, g.2, one_mul]

@[expose] def transv (a b : Fin 4) (hab : a ≠ b) (c : K) : Matrix.SpecialLinearGroup (Fin 4) K :=
  ⟨Matrix.transvection a b c, Matrix.det_transvection_of_ne a b hab c⟩

theorem quadPlus_single_inl (i : Fin 3) : quadPlus 3 K (Pi.single (.inl i) 1) = 0 :=
  quadPlus_plusVec 3 K i true

theorem quadPlus_single_inr (i : Fin 3) : quadPlus 3 K (Pi.single (.inr i) 1) = 0 :=
  quadPlus_plusVec 3 K i false

theorem rho_transv_01 (c : K) :
    rhoGL (transv 0 1 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 2 true) (c • plusVec 3 K 1 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 2 true) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_10 (c : K) :
    rhoGL (transv 1 0 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 1 false) (c • plusVec 3 K 2 false) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 1 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inr]
  all_goals ring

theorem rho_transv_02 (c : K) :
    rhoGL (transv 0 2 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 0 true) (c • plusVec 3 K 2 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 0 true) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_20 (c : K) :
    rhoGL (transv 2 0 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 2 false) (c • plusVec 3 K 0 false) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 2 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inr]
  all_goals ring

theorem rho_transv_03 (c : K) :
    rhoGL (transv 0 3 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 1 true) (c • plusVec 3 K 0 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 1 true) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_30 (c : K) :
    rhoGL (transv 3 0 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 0 false) (c • plusVec 3 K 1 false) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 0 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inr]
  all_goals ring

theorem rho_transv_12 (c : K) :
    rhoGL (transv 1 2 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 1 false) (c • plusVec 3 K 0 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 1 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_21 (c : K) :
    rhoGL (transv 2 1 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 0 false) (c • plusVec 3 K 1 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 0 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_13 (c : K) :
    rhoGL (transv 1 3 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 2 false) (c • plusVec 3 K 0 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 2 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_31 (c : K) :
    rhoGL (transv 3 1 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 0 false) (c • plusVec 3 K 2 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 0 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_23 (c : K) :
    rhoGL (transv 2 3 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 2 false) (c • plusVec 3 K 1 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 2 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

theorem rho_transv_32 (c : K) :
    rhoGL (transv 3 2 (by decide) c) =
      eichler (quadPlus 3 K) (plusVec 3 K 1 false) (c • plusVec 3 K 2 true) := by
  refine LinearEquiv.ext fun v => ?_
  rw [rhoGL_apply, eichler_apply (quadPlus_plusVec 3 K 1 false) (by
    rw [polar_smul_right, polar_quadPlus_plusVec]; simp)]
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [transv, coordsOf, skewOf, antiMat, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      QuadraticMap.map_smul, quadPlus_single_inl]
  all_goals ring

end CFSG.ComponentClassification.CatLeafProof.KleinSix
