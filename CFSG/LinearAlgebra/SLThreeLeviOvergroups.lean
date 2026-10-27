module

public import CFSG.LinearAlgebra.SLThreeLeviRadical
public import CFSG.LinearAlgebra.LinearGroups.SLThreeRootGeneration
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQBorel

public section

open Matrix
open CFSG.RankThree.SubgroupLists
open CFSG.RankThree.PartTwo.Sec4.L34Odd (embSL embSL_coe)
open scoped MatrixGroups

namespace CFSG.LinearAlgebra.SLThreeLevi

variable {K : Type*} [Field K]

private theorem exists_lowerElem_of_blockb_eq_zero
    (H : Subgroup (SL(3, K))) (hD : levi ≤ H) {g : SL(3, K)}
    (hgH : g ∈ H) (hgD : g ∉ levi)
    (hb : blockb (g : Matrix (Fin 3) (Fin 3) K) = 0) :
    ∃ v : Fin 2 → K, lowerElem v ∈ H ∧ lowerElem v ≠ 1 := by
  let M : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K)
  let A : Matrix (Fin 2) (Fin 2) K := ulBlock M
  let c : Fin 2 → K := blockc M
  let d : K := blockd M
  have hM : blockMat A 0 c d = M := by
    have h := blockMat_ulBlock_blockb_blockc_blockd M
    rw [hb] at h
    simpa [A, c, d] using h
  have hdetAd : A.det * d = 1 := by
    have h : M.det = 1 := g.2
    rw [← hM, blockMat_det_zero_upper] at h
    exact h
  have hAdet : A.det ≠ 0 := left_ne_zero_of_mul_eq_one hdetAd
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one hdetAd
  let Aunit : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet
  have hAunit : (Aunit : Matrix (Fin 2) (Fin 2) K) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hAdet
  have hLmem : embSL Aunit ∈ H :=
    hD (mem_levi_iff.mpr ⟨Aunit, rfl⟩)
  have hLinv : (embSL Aunit)⁻¹ ∈ H := H.inv_mem hLmem
  by_cases hc0 : c = 0
  · have hMeq : g = embSL Aunit := by
      apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
      change M = ((embSL Aunit : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
      rw [← hM, embSL_coe_blockMat, hAunit, hc0]
      have hd_eq : d = (A.det)⁻¹ := by
        refine mul_left_cancel₀ hAdet ?_
        rw [hdetAd, mul_inv_cancel₀ hAdet]
      rw [hd_eq]
    exact absurd (by rw [hMeq]; exact mem_levi_iff.mpr ⟨Aunit, rfl⟩) hgD
  · let r : Fin 2 → K := c ᵥ* (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    have hAAinv : A * (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
      rw [← hAunit, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hprod : g * (embSL Aunit)⁻¹ = lowerElem r := by
      apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
      change M * (((embSL Aunit)⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        (lowerElem r : Matrix (Fin 3) (Fin 3) K)
      rw [← hM, embSL_inv_coe_blockMat]
      change blockMat A 0 c d *
          blockMat (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0
            (A.det) = blockMat 1 0 r 1
      rw [blockMat_mul, blockMat_inj]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAAinv, Matrix.vecMulVec_zero, add_zero]
      · funext i
        simp
      · funext j
        simp [r]
      · rw [dotProduct_zero, zero_add, mul_comm, hdetAd]
    have hr_ne : r ≠ 0 := by
      intro hr
      have hc : c = 0 := by
        calc c = c ᵥ* (1 : Matrix (Fin 2) (Fin 2) K) := by simp
          _ = c ᵥ* ((((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
                (Aunit : Matrix (Fin 2) (Fin 2) K)) := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          _ = (c ᵥ* (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) ᵥ*
                (Aunit : Matrix (Fin 2) (Fin 2) K) := by rw [Matrix.vecMul_vecMul]
          _ = 0 := by
              rw [show c ᵥ* (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 0 from hr,
                Matrix.zero_vecMul]
      exact hc0 hc
    have hne : lowerElem r ≠ 1 := by
      intro h
      apply hr_ne
      exact lowerElem_injective (by simpa [lowerElem_zero] using h)
    exact ⟨r, by rw [← hprod]; exact H.mul_mem hgH hLinv, hne⟩

private theorem exists_upperElem_of_blockc_eq_zero
    (H : Subgroup (SL(3, K))) (hD : levi ≤ H) {g : SL(3, K)}
    (hgH : g ∈ H) (hgD : g ∉ levi)
    (hc : blockc (g : Matrix (Fin 3) (Fin 3) K) = 0) :
    ∃ v : Fin 2 → K, upperElem v ∈ H ∧ upperElem v ≠ 1 := by
  let M : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K)
  let A : Matrix (Fin 2) (Fin 2) K := ulBlock M
  let b : Fin 2 → K := blockb M
  let d : K := blockd M
  have hM : blockMat A b 0 d = M := by
    have h := blockMat_ulBlock_blockb_blockc_blockd M
    rw [hc] at h
    simpa [A, b, d] using h
  have hdetAd : A.det * d = 1 := by
    have h : M.det = 1 := g.2
    rw [← hM, blockMat_det_zero_lower] at h
    exact h
  have hAdet : A.det ≠ 0 := left_ne_zero_of_mul_eq_one hdetAd
  let Aunit : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet
  have hAunit : (Aunit : Matrix (Fin 2) (Fin 2) K) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hAdet
  have hLmem : embSL Aunit ∈ H :=
    hD (mem_levi_iff.mpr ⟨Aunit, rfl⟩)
  have hLinv : (embSL Aunit)⁻¹ ∈ H := H.inv_mem hLmem
  by_cases hb0 : b = 0
  · have hMeq : g = embSL Aunit := by
      apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
      change M = ((embSL Aunit : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
      rw [← hM, embSL_coe_blockMat, hAunit, hb0]
      have hd_eq : d = (A.det)⁻¹ := by
        refine mul_left_cancel₀ hAdet ?_
        rw [hdetAd, mul_inv_cancel₀ hAdet]
      rw [hd_eq]
    exact absurd (by rw [hMeq]; exact mem_levi_iff.mpr ⟨Aunit, rfl⟩) hgD
  · let r : Fin 2 → K := fun i => b i * A.det
    have hAAinv : A * (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
      rw [← hAunit, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hprod : g * (embSL Aunit)⁻¹ = upperElem r := by
      apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
      change M * (((embSL Aunit)⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        (upperElem r : Matrix (Fin 3) (Fin 3) K)
      rw [← hM, embSL_inv_coe_blockMat]
      change blockMat A b 0 d *
          blockMat (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0
            (A.det) = blockMat 1 r 0 1
      rw [blockMat_mul, blockMat_inj]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAAinv, Matrix.vecMulVec_zero, add_zero]
      · funext i
        simp [r]
      · funext j
        simp
      · rw [dotProduct_zero, zero_add, mul_comm, hdetAd]
    have hr_ne : r ≠ 0 := by
      intro hr
      have hb : b = 0 := by
        funext i
        have hi := congrFun hr i
        simp [r] at hi
        exact hi.resolve_right hAdet
      exact hb0 hb
    have hne : upperElem r ≠ 1 := by
      intro h
      apply hr_ne
      exact upperElem_injective (by simpa [upperElem_zero] using h)
    exact ⟨r, by rw [← hprod]; exact H.mul_mem hgH hLinv, hne⟩

private theorem detA_ne_zero_of_condition {A : Matrix (Fin 2) (Fin 2) K} {b c : Fin 2 → K} {d : K}
    {u : Fin 2 → K} (hdM : (blockMat A b c d).det ≠ 0)
    (hu : A *ᵥ u = b) (hcu : c ⬝ᵥ u = 0) : A.det ≠ 0 := by
  by_contra hAdet
  have hAdet0 : A.det = 0 := by simpa using hAdet
  obtain ⟨v, hvne, hvker⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hAdet0
  have hemb2_v_ne : emb2 v ≠ 0 := by
    intro h
    exact hvne (emb2_eq_zero_iff.mp h)
  have hv_e3 : blockMat A b c d *ᵥ emb2 v = (c ⬝ᵥ v) • e3 := by
    rw [blockMat_mulVec_emb2, hvker]
    simp
  have hcv_ne : c ⬝ᵥ v ≠ 0 := by
    intro hcv0
    have hzero : blockMat A b c d *ᵥ emb2 v = 0 := by
      rw [hv_e3, hcv0]
      simp
    exact hemb2_v_ne (Matrix.eq_zero_of_mulVec_eq_zero hdM hzero)
  have he3 : blockMat A b c d *ᵥ ((c ⬝ᵥ v)⁻¹ • emb2 v) = e3 := by
    rw [Matrix.mulVec_smul, hv_e3, smul_smul, inv_mul_cancel₀ hcv_ne, one_smul]
  have hMu : blockMat A b c d *ᵥ emb2 u = emb2 b := by
    rw [blockMat_mulVec_emb2, hu, hcu]
    simp
  have hMe3 : blockMat A b c d *ᵥ e3 = emb2 b + d • e3 := blockMat_mulVec_e3 A b c d
  have hsum : blockMat A b c d *ᵥ
      (emb2 u + d • ((c ⬝ᵥ v)⁻¹ • emb2 v)) = emb2 b + d • e3 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hMu, he3]
  have hinj : Function.Injective (blockMat A b c d).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero hdM
  have heq : emb2 u + d • ((c ⬝ᵥ v)⁻¹ • emb2 v) = e3 :=
    hinj (hsum.trans hMe3.symm)
  have h2 := congrFun heq 2
  simp [emb2, e3] at h2

private def e1 : Fin 2 → K := ![1, 0]

@[simp] private theorem e1_eq_single : e1 = Pi.single 0 (1 : K) := by
  funext i
  fin_cases i <;> simp [e1]

private theorem exists_lowerElem_of_exceptional
    (H : Subgroup (SL(3, K))) (hD : levi ≤ H) {a : K}
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) {g2 : SL(3, K)} (hg2H : g2 ∈ H)
    (hform : (g2 : Matrix (Fin 3) (Fin 3) K) = blockMat 1 e1
      (fun j => if j = 0 then 0 else a) 1) :
    ∃ v : Fin 2 → K, lowerElem v ∈ H ∧ lowerElem v ≠ 1 := by
  let g2Inv : SL(3, K) :=
    ⟨!![1, a, -1; 0, 1, 0; 0, -a, 1], by
      simp [Matrix.det_fin_three]⟩
  have hg2Inv : g2 * g2Inv = 1 := by
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    rw [hform]
    change blockMat 1 e1 (fun j => if j = 0 then 0 else a) 1 *
      ((g2Inv : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMat, e1, g2Inv, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hg2Inv_eq : g2⁻¹ = g2Inv := inv_eq_of_mul_eq_one_right hg2Inv
  let v : Fin 2 → K := fun j => if j = 0 then 0 else -2 * a
  have hv_ne : v ≠ 0 := by
    intro hv
    have h1 := congrFun hv 1
    simp [v] at h1
    have : a = 0 := h1.resolve_left h2
    exact ha this
  have hcomm : (negDiagElem * g2 * negDiagElem⁻¹) * g2⁻¹ = lowerElem v := by
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [negDiagElem_inv, hg2Inv_eq, hform]
    change ((negDiagElem : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        blockMat 1 e1 (fun j => if j = 0 then 0 else a) 1 *
        ((negDiagElem : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        ((g2Inv : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((lowerElem v : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMat, e1, v, negDiagElem_coe, g2Inv, lowerElem,
        Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hmem : negDiagElem ∈ H := hD negDiag_mem_levi
  have hcommH : (negDiagElem * g2 * negDiagElem⁻¹) * g2⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hmem hg2H) (H.inv_mem hmem)) (H.inv_mem hg2H)
  have hne : lowerElem v ≠ 1 := by
    intro h
    apply hv_ne
    exact lowerElem_injective (by simpa [lowerElem_zero] using h)
  exact ⟨v, by rw [← hcomm]; exact hcommH, hne⟩

private theorem exists_gl2_mulVec_eq_e1 {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ P : GL (Fin 2) K, (P : Matrix (Fin 2) (Fin 2) K) *ᵥ v = e1 ∧
      (P : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  obtain ⟨S, hS0, hS1⟩ := CFSG.ABGLocalTools.exists_sl2_first_column hv
  have hS : ((S : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = v := by
    ext i
    fin_cases i <;>
      simp [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hS0, hS1]
  refine ⟨SpecialLinearGroup.toGL S⁻¹, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    calc (((S⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v
        = (((S⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ
            (((S : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ e1) := by
            rw [hS]
      _ = ((((S⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
            ((S : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ e1 := by
            rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ e1 := by
            rw [show (((S⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
                ((S : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 by
              rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.SpecialLinearGroup.coe_one]]
      _ = e1 := by rw [Matrix.one_mulVec]
  · simpa [Matrix.GeneralLinearGroup.val_det_apply] using (S⁻¹).2

private theorem blockMat_conj_one (P : GL (Fin 2) K) (v w : Fin 2 → K) :
    blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 1 * blockMat 1 v w 1 *
        blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
      blockMat 1 ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
        (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) 1 := by
  have hPPinv : (P : Matrix (Fin 2) (Fin 2) K) *
      (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [blockMat_mul, blockMat_mul, blockMat_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.vecMulVec_zero, hPPinv]
  · funext i
    simp
  · funext j
    simp
  · simp

private theorem detA_mul_d_eq_one_of_condition {A : Matrix (Fin 2) (Fin 2) K} {b c : Fin 2 → K}
    {d : K} {u : Fin 2 → K} (hMdet : (blockMat A b c d).det = 1)
    (hu : A *ᵥ u = b) (hcu : c ⬝ᵥ u = 0) : A.det * d = 1 := by
  have hAdet : A.det ≠ 0 :=
    detA_ne_zero_of_condition (by rw [hMdet]; exact one_ne_zero) hu hcu
  let Aunit : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet
  have hAunit : (Aunit : Matrix (Fin 2) (Fin 2) K) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hAdet
  let v : Fin 2 → K := (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ b
  have hAv : A *ᵥ v = b := by
    rw [show A = (Aunit : Matrix (Fin 2) (Fin 2) K) from hAunit.symm,
      Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hu_eq : u = v := by
    apply Matrix.mulVec_injective_of_det_ne_zero hAdet
    rw [hu, hAv]
  have hcv : c ⬝ᵥ v = 0 := by rw [← hu_eq]; exact hcu
  let beta : Fin 2 → K := -v
  have hAbeta : A *ᵥ beta = -b := by
    simp [beta, Matrix.mulVec_neg, hAv]
  have hcbeta : c ⬝ᵥ beta = 0 := by
    simp [beta, hcv]
  have hprod : blockMat A b c d * blockMat 1 beta 0 1 = blockMat A 0 c d := by
    rw [blockMat_mul, blockMat_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.vecMulVec_zero, add_zero, Matrix.mul_one]
    · funext i
      simp [hAbeta]
    · funext j
      simp
    · simp [hcbeta]
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hMdet, blockMat_det_upper,
    blockMat_det_zero_upper] at hdet
  simpa using hdet.symm

private theorem exists_lowerElem_of_condition
    (H : Subgroup (SL(3, K))) (hD : levi ≤ H) {g : SL(3, K)}
    (hgH : g ∈ H) (hgD : g ∉ levi) {A : Matrix (Fin 2) (Fin 2) K}
    {b c : Fin 2 → K} {d : K}
    (hM : blockMat A b c d = (g : Matrix (Fin 3) (Fin 3) K))
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hcond : ∃ u : Fin 2 → K, A *ᵥ u = b ∧ c ⬝ᵥ u = 0)
    (h2 : (2 : K) ≠ 0) :
    ∃ v : Fin 2 → K, lowerElem v ∈ H ∧ lowerElem v ≠ 1 := by
  obtain ⟨u, hu, hcu⟩ := hcond
  have hMdet : (blockMat A b c d).det = 1 := by rw [hM]; exact g.2
  have hAdet : A.det ≠ 0 := detA_ne_zero_of_condition (by rw [hMdet]; exact one_ne_zero) hu hcu
  have hdetAd : A.det * d = 1 := detA_mul_d_eq_one_of_condition hMdet hu hcu
  let Aunit : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet
  have hAunit : (Aunit : Matrix (Fin 2) (Fin 2) K) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hAdet
  let v : Fin 2 → K := (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ b
  have hAv : A *ᵥ v = b := by
    rw [show A = (Aunit : Matrix (Fin 2) (Fin 2) K) from hAunit.symm,
      Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro hv0
    apply hb
    rw [← hAv, hv0, Matrix.mulVec_zero]
  have hcv : c ⬝ᵥ v = 0 := by
    have hu_eq : u = v := by
      apply Matrix.mulVec_injective_of_det_ne_zero hAdet
      rw [hu, hAv]
    rw [← hu_eq]
    exact hcu
  let w : Fin 2 → K := A.det • c
  have hwne : w ≠ 0 := by
    intro hw0
    apply hc
    funext i
    have hi := congrFun hw0 i
    simp [w] at hi
    exact hi.resolve_left hAdet
  have hwv : w ⬝ᵥ v = 0 := by
    simp [w, hcv]
  have hAAinv : (Aunit : Matrix (Fin 2) (Fin 2) K) *
      (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAinvA : (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      (Aunit : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let g1 : SL(3, K) := (embSL Aunit)⁻¹ * g
  have hg1H : g1 ∈ H :=
    H.mul_mem (H.inv_mem (hD (mem_levi_iff.mpr ⟨Aunit, rfl⟩))) hgH
  have hg1 : (g1 : Matrix (Fin 3) (Fin 3) K) = blockMat 1 v w 1 := by
    show (((embSL Aunit)⁻¹ * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blockMat 1 v w 1
    rw [Matrix.SpecialLinearGroup.coe_mul, embSL_inv_coe_blockMat, ← hM, hAunit]
    change blockMat (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0
        (Aunit : Matrix (Fin 2) (Fin 2) K).det * blockMat A b c d = blockMat 1 v w 1
    rw [← hAunit]
    change blockMat (((Aunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0
        (Aunit : Matrix (Fin 2) (Fin 2) K).det *
      blockMat (Aunit : Matrix (Fin 2) (Fin 2) K) b c d = blockMat 1 v w 1
    rw [blockMat_mul, blockMat_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hAinvA
    · funext i
      simp [v]
    · have hdetAunit : (Aunit : Matrix (Fin 2) (Fin 2) K).det = A.det := by rw [hAunit]
      funext j
      simp [w, Pi.smul_apply, hdetAunit]
    · simpa [hAunit] using hdetAd
  obtain ⟨P, hPv, hPdet⟩ := exists_gl2_mulVec_eq_e1 hvne
  have hPPinv : (P : Matrix (Fin 2) (Fin 2) K) *
      (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPinvP : (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      (P : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let g2 : SL(3, K) := embSL P * g1 * (embSL P)⁻¹
  have hg2H : g2 ∈ H :=
    H.mul_mem (H.mul_mem (hD (mem_levi_iff.mpr ⟨P, rfl⟩)) hg1H)
      (H.inv_mem (hD (mem_levi_iff.mpr ⟨P, rfl⟩)))
  have hPinv_e1 : (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ e1 = v := by
    calc (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ e1
        = (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ
            ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by rw [hPv]
      _ = ((((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
            (P : Matrix (Fin 2) (Fin 2) K)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by rw [hPinvP]
      _ = v := by rw [Matrix.one_mulVec]
  have hwPinv0 : (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) 0 = 0 := by
    calc (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) 0
        = w ⬝ᵥ ((((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ e1) := by
            simp [Matrix.vecMul, Matrix.mulVec, dotProduct, e1, Fin.sum_univ_two]
      _ = w ⬝ᵥ v := by rw [hPinv_e1]
      _ = 0 := hwv
  let a : K := (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) 1
  have hwrow : (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) =
      fun j => if j = 0 then 0 else a := by
    funext j
    fin_cases j
    · simpa using hwPinv0
    · simp [a]
  have hane : a ≠ 0 := by
    intro ha0
    have hrow0 : (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) = 0 := by
      funext j
      fin_cases j
      · simpa using hwPinv0
      · simpa [a] using ha0
    have hw0 : w = 0 := by
      calc w = (w ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) ᵥ*
            (P : Matrix (Fin 2) (Fin 2) K) := by
              rw [Matrix.vecMul_vecMul, hPinvP, Matrix.vecMul_one]
        _ = 0 := by rw [hrow0, Matrix.zero_vecMul]
    exact hwne hw0
  have hg2 : (g2 : Matrix (Fin 3) (Fin 3) K) =
      blockMat 1 e1 (fun j => if j = 0 then 0 else a) 1 := by
    show ((embSL P * g1 * (embSL P)⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blockMat 1 e1 (fun j => if j = 0 then 0 else a) 1
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [hg1, embSL_coe_blockMat, embSL_inv_coe_blockMat, hPdet, inv_one]
    rw [blockMat_conj_one P v w, hPv, hwrow]
  exact exists_lowerElem_of_exceptional H hD hane h2 hg2H hg2

private theorem tMat_mulVec {b ell x : Fin 2 → K} :
    (1 + Matrix.vecMulVec b ell : Matrix (Fin 2) (Fin 2) K) *ᵥ x =
      x + (ell ⬝ᵥ x) • b := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

private theorem tMat_mulVec_self {b ell : Fin 2 → K} (hell : ell ⬝ᵥ b = 0) :
    (1 + Matrix.vecMulVec b ell : Matrix (Fin 2) (Fin 2) K) *ᵥ b = b := by
  rw [tMat_mulVec, hell, zero_smul, add_zero]

private theorem transvection_conj_block
    {A : Matrix (Fin 2) (Fin 2) K} {b c : Fin 2 → K} {d : K} {ell : Fin 2 → K}
    (hell : ell ⬝ᵥ b = 0) {g t h : SL(3, K)}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = blockMat A b c d)
    (ht : (t : Matrix (Fin 3) (Fin 3) K) =
      blockMat (1 + Matrix.vecMulVec b ell : Matrix (Fin 2) (Fin 2) K) 0 0 1)
    (hdef : h = g⁻¹ * t * g) :
    (h : Matrix (Fin 3) (Fin 3) K) *ᵥ e3 = e3 ∧
      ∀ j : Fin 2,
        (h : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1) =
          Pi.single j.castSucc 1 +
            (ell ⬝ᵥ (A *ᵥ (Pi.single j 1))) •
              (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ emb2 b) := by
  have hginv : (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *
      (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hhmat : (h : Matrix (Fin 3) (Fin 3) K) =
      (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *
        (t : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [hdef]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hg3 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e3 = emb2 b + d • e3 := by
    rw [hg, blockMat_mulVec_e3]
  have ht3 : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ e3 = e3 := by
    rw [ht, blockMat_mulVec_e3]
    simp
  have htb : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ emb2 b = emb2 b := by
    rw [ht, blockMat_mulVec_emb2, tMat_mulVec_self hell]
    simp
  have htge3 : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ e3) = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e3 := by
    rw [hg3, Matrix.mulVec_add, Matrix.mulVec_smul, htb, ht3]
  constructor
  · calc (h : Matrix (Fin 3) (Fin 3) K) *ᵥ e3
        = ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *
            (t : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ e3 := by
            rw [hhmat]
      _ = (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
            ((t : Matrix (Fin 3) (Fin 3) K) *ᵥ
              ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ e3)) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ e3) := by rw [htge3]
      _ = ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *
            (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ e3 := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ e3 := by rw [hginv]
      _ = e3 := by rw [Matrix.one_mulVec]
  · intro j
    have hgj : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1) =
        emb2 (A *ᵥ (Pi.single j 1)) + c j • e3 := by
      rw [hg, blockMat_mulVec_first]
    have htcol : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1)) =
        (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1) +
          (ell ⬝ᵥ (A *ᵥ (Pi.single j 1))) • emb2 b := by
      rw [hgj, Matrix.mulVec_add, Matrix.mulVec_smul, ht, blockMat_mulVec_emb2,
        tMat_mulVec, blockMat_mulVec_e3]
      simp [emb2_add, emb2_smul, add_assoc, add_comm, add_left_comm]
    calc (h : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1)
        = ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *
            (t : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ
              (Pi.single j.castSucc 1) := by rw [hhmat]
      _ = (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
            ((t : Matrix (Fin 3) (Fin 3) K) *ᵥ
              ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1))) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j.castSucc 1) +
              (ell ⬝ᵥ (A *ᵥ (Pi.single j 1))) • emb2 b) := by rw [htcol]
      _ = ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *
            (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ (Pi.single j.castSucc 1) +
          (ell ⬝ᵥ (A *ᵥ (Pi.single j 1))) •
            (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ emb2 b) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      _ = Pi.single j.castSucc 1 +
          (ell ⬝ᵥ (A *ᵥ (Pi.single j 1))) •
            (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ emb2 b) := by
            rw [hginv, Matrix.one_mulVec]

private theorem ellA_ne_zero {A : Matrix (Fin 2) (Fin 2) K} {b c : Fin 2 → K} {d : K}
    (hb : b ≠ 0) (hdM : (blockMat A b c d).det ≠ 0) :
    (fun j => b 1 * A 0 j - b 0 * A 1 j) ≠ 0 := by
  intro hzero
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdM
  have hcomp := hrows.comp (fun i : Fin 2 => i.castSucc) (Fin.castAdd_injective 2 1)
  have hpair : LinearIndependent K
      ![(fun j => blockMat A b c d 0 j), (fun j => blockMat A b c d 1 j)] := by
    convert hcomp using 1
    funext i
    fin_cases i <;> rfl
  have hrel : b 1 • (fun j => blockMat A b c d 0 j) =
      b 0 • (fun j => blockMat A b c d 1 j) := by
    funext j
    fin_cases j
    · have h := sub_eq_zero.mp (congrFun hzero 0)
      simpa [blockMat] using h
    · have h := sub_eq_zero.mp (congrFun hzero 1)
      simpa [blockMat] using h
    · simp [blockMat]
      ring
  have hcoeff := hpair.eq_zero_of_pair' hrel
  apply hb
  funext i
  fin_cases i
  · exact hcoeff.2
  · exact hcoeff.1

private theorem exists_lowerElem_of_not_condition
    (H : Subgroup (SL(3, K))) (hD : levi ≤ H) {g : SL(3, K)}
    (hgH : g ∈ H) (hgD : g ∉ levi) {A : Matrix (Fin 2) (Fin 2) K}
    {b c : Fin 2 → K} {d : K}
    (hM : blockMat A b c d = (g : Matrix (Fin 3) (Fin 3) K))
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hnot : ¬ ∃ u : Fin 2 → K, A *ᵥ u = b ∧ c ⬝ᵥ u = 0)
    (h2 : (2 : K) ≠ 0) :
    ∃ v : Fin 2 → K, lowerElem v ∈ H ∧ lowerElem v ≠ 1 := by
  have hMdet : (blockMat A b c d).det = 1 := by rw [hM]; exact g.2
  have hMdet_ne : (blockMat A b c d).det ≠ 0 := by rw [hMdet]; exact one_ne_zero
  let ell : Fin 2 → K := ![b 1, -b 0]
  have hell : ell ⬝ᵥ b = 0 := by
    simp [ell, dotProduct, Fin.sum_univ_two]
    ring
  have hEllA_ne : (fun j => ell ⬝ᵥ (A *ᵥ Pi.single j 1)) ≠ 0 := by
    have h := ellA_ne_zero hb hMdet_ne
    convert h using 1
    funext j
    fin_cases j <;>
      simp [ell, dotProduct, Matrix.mulVec, Pi.single, Fin.sum_univ_two] <;>
      ring
  let tMat : Matrix (Fin 2) (Fin 2) K := 1 + Matrix.vecMulVec b ell
  have htMat_det : tMat.det = 1 := by
    have hell' : ell 0 * b 0 + ell 1 * b 1 = 0 := by
      simpa [dotProduct, Fin.sum_univ_two] using hell
    simp [tMat, Matrix.det_fin_two, Matrix.vecMulVec]
    linear_combination hell'
  let Aunit : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero tMat
    (by rw [htMat_det]; exact one_ne_zero)
  let t : SL(3, K) := embSL Aunit
  have ht : (t : Matrix (Fin 3) (Fin 3) K) = blockMat tMat 0 0 1 := by
    rw [embSL_coe_blockMat, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      htMat_det, inv_one]
  have htH : t ∈ H := hD (mem_levi_iff.mpr ⟨Aunit, rfl⟩)
  have hgInvH : g⁻¹ ∈ H := H.inv_mem hgH
  let h : SL(3, K) := g⁻¹ * t * g
  have hhH : h ∈ H := H.mul_mem (H.mul_mem hgInvH htH) hgH
  have hhmat : (h : Matrix (Fin 3) (Fin 3) K) =
      (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        (t : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) := by
    simp [h, Matrix.SpecialLinearGroup.coe_mul]
  have hprops := transvection_conj_block hell hM.symm ht rfl
  let v : Fin 3 → K := (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ emb2 b)
  have hv3 : v 2 ≠ 0 := by
    intro hv2
    let u : Fin 2 → K := fun i => v i.castSucc
    have hv_eq : v = emb2 u := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · simpa [emb2] using hv2
    have hgginv : (g : Matrix (Fin 3) (Fin 3) K) *
        (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = emb2 b := by
      calc (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v
          = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
              ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ emb2 b) := rfl
        _ = ((g : Matrix (Fin 3) (Fin 3) K) *
              (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))) *ᵥ emb2 b := by
              rw [Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ emb2 b := by rw [hgginv]
        _ = emb2 b := by rw [Matrix.one_mulVec]
    have hgu : (blockMat A b c d) *ᵥ emb2 u = emb2 b := by
      rw [hM, ← hv_eq]
      exact hgv
    rw [blockMat_mulVec_emb2] at hgu
    have hcu : c ⬝ᵥ u = 0 := by
      have := congrFun hgu 2
      simpa [emb2, e3] using this
    have hAu : A *ᵥ u = b := by
      apply emb2_injective
      simpa [hcu] using hgu
    exact hnot ⟨u, hAu, hcu⟩
  have hb0 : blockb (h : Matrix (Fin 3) (Fin 3) K) = 0 := by
    funext i
    fin_cases i
    · have hcol := congrFun hprops.1 0
      rw [e3_eq_single, Matrix.mulVec_single_one, Matrix.col_apply] at hcol
      rw [blockb, hhmat]
      simpa [e3] using hcol
    · have hcol := congrFun hprops.1 1
      rw [e3_eq_single, Matrix.mulVec_single_one, Matrix.col_apply] at hcol
      rw [blockb, hhmat]
      simpa [e3] using hcol
  have hcne : blockc (h : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
    intro hc0
    apply hEllA_ne
    funext j
    have hcol := congrFun (hprops.2 j) 2
    have hj := congrFun hc0 j
    have hformula : blockc (h : Matrix (Fin 3) (Fin 3) K) j =
        (ell ⬝ᵥ (A *ᵥ Pi.single j 1)) * v 2 := by
      fin_cases j
      all_goals
        rw [Matrix.mulVec_single_one, Matrix.col_apply] at hcol
        rw [blockc, hhmat]
        simpa [v, Pi.single, ell] using hcol
    rw [hformula] at hj
    exact (mul_eq_zero.mp hj).resolve_right hv3
  have hhD : h ∉ levi := by
    intro hlev
    exact hcne (levi_blockc_eq_zero hlev)
  exact exists_lowerElem_of_blockb_eq_zero H hD hhH hhD hb0

theorem exists_radical_of_not_le_levi (H : Subgroup (SL(3, K))) (hD : levi ≤ H)
    (h2 : (2 : K) ≠ 0) {g : SL(3, K)} (hgH : g ∈ H) (hgD : g ∉ levi) :
    (∃ u : Fin 2 → K, upperElem u ∈ H ∧ upperElem u ≠ 1) ∨
      (∃ v : Fin 2 → K, lowerElem v ∈ H ∧ lowerElem v ≠ 1) := by
  let M : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K)
  let A : Matrix (Fin 2) (Fin 2) K := ulBlock M
  let b : Fin 2 → K := blockb M
  let c : Fin 2 → K := blockc M
  let d : K := blockd M
  have hM : blockMat A b c d = M := by
    have h := blockMat_ulBlock_blockb_blockc_blockd M
    simpa [A, b, c, d] using h
  by_cases hb : b = 0
  · exact Or.inr (exists_lowerElem_of_blockb_eq_zero H hD hgH hgD (by simpa [b, M] using hb))
  by_cases hc : c = 0
  · exact Or.inl (exists_upperElem_of_blockc_eq_zero H hD hgH hgD (by simpa [c, M] using hc))
  · by_cases hcond : ∃ u : Fin 2 → K, A *ᵥ u = b ∧ c ⬝ᵥ u = 0
    · exact Or.inr (exists_lowerElem_of_condition H hD hgH hgD hM hb hc hcond h2)
    · exact Or.inr (exists_lowerElem_of_not_condition H hD hgH hgD hM hb hc hcond h2)

private theorem embSL_conj_upper (P : GL (Fin 2) K) (hP : (P : Matrix (Fin 2) (Fin 2) K).det = 1)
    (u : Fin 2 → K) :
    embSL P * upperElem u * (embSL P)⁻¹ = upperElem ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ u) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply, Matrix.SpecialLinearGroup.coe_mul]
  rw [embSL_coe_blockMat, embSL_inv_coe_blockMat, hP, inv_one]
  change blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 1 * blockMat 1 u 0 1 *
      blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
    blockMat 1 ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ u) 0 1
  rw [blockMat_conj_one P u 0]
  simp

private theorem embSL_conj_lower (P : GL (Fin 2) K) (hP : (P : Matrix (Fin 2) (Fin 2) K).det = 1)
    (u : Fin 2 → K) :
    embSL P * lowerElem u * (embSL P)⁻¹ =
      lowerElem (u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply, Matrix.SpecialLinearGroup.coe_mul]
  rw [embSL_coe_blockMat, embSL_inv_coe_blockMat, hP, inv_one]
  change blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 1 * blockMat 1 0 u 1 *
      blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
    blockMat 1 0 (u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) 1
  rw [blockMat_conj_one P 0 u]
  simp

private theorem embSL_inv_conj_lower (R : GL (Fin 2) K)
    (hRinv_det : (((R⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1)
    (u : Fin 2 → K) :
    (embSL R)⁻¹ * lowerElem u * ((embSL R)⁻¹)⁻¹ =
      lowerElem (u ᵥ* (R : Matrix (Fin 2) (Fin 2) K)) := by
  rw [← map_inv]
  rw [embSL_conj_lower R⁻¹ hRinv_det u, inv_inv]

private theorem exists_gl2_vecMul_inv_eq_e1 {c : Fin 2 → K} (hc : c ≠ 0) :
    ∃ Q : GL (Fin 2) K,
      c ᵥ* (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = Pi.single 0 1 ∧
        (Q : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  obtain ⟨P, hPc, hPdet⟩ := exists_gl2_mulVec_eq_e1 hc
  let Q : GL (Fin 2) K := Matrix.GeneralLinearGroup.inverseTranspose P
  have hQdet : (Q : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [show (Q : Matrix (Fin 2) (Fin 2) K) =
        (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ from
      Matrix.GeneralLinearGroup.coe_inverseTranspose P, Matrix.det_transpose,
      ← Matrix.GeneralLinearGroup.val_inv_det_apply P, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply P, hPdet, inv_one]
  have hQinv : (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      (P : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    have hIQ : Matrix.GeneralLinearGroup.inverseTranspose Q = P := by
      rw [show Matrix.GeneralLinearGroup.inverseTranspose Q = P from
        Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose P]
    have hIQcoe := congrArg (fun x : GL (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K)) hIQ
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose] at hIQcoe
    have htrans := congrArg Matrix.transpose hIQcoe
    simpa [Matrix.transpose_transpose] using htrans
  refine ⟨Q, ?_, hQdet⟩
  rw [hQinv, Matrix.vecMul_transpose, hPc, e1_eq_single]

theorem upperRadical_le_of_exists (H : Subgroup (SL(3, K))) (hD : levi ≤ H)
    (hex : ∃ u : Fin 2 → K, upperElem u ∈ H ∧ upperElem u ≠ 1) :
    upperRadical ≤ H := by
  obtain ⟨u, huH, hune⟩ := hex
  have hu_ne : u ≠ 0 := by
    intro hu0
    apply hune
    rw [hu0, upperElem_zero]
  obtain ⟨P, hPu, hPdet⟩ := exists_gl2_mulVec_eq_e1 hu_ne
  have hPmem : embSL P ∈ H := hD (mem_levi_iff.mpr ⟨P, rfl⟩)
  have hPinv_mem : (embSL P)⁻¹ ∈ H := H.inv_mem hPmem
  have he1_mem : upperElem e1 ∈ H := by
    rw [← hPu, ← embSL_conj_upper P hPdet u]
    exact H.mul_mem (H.mul_mem hPmem huH) hPinv_mem
  intro g hg
  rw [mem_upperRadical_iff] at hg
  obtain ⟨b, rfl⟩ := hg
  by_cases hb : b = 0
  · rw [hb, upperElem_zero]
    exact H.one_mem
  · obtain ⟨Q, hQb, hQdet⟩ := exists_gl2_mulVec_eq_e1 hb
    have hQinv_det : (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_inv_det_apply Q, Units.val_inv_eq_inv_val,
        Matrix.GeneralLinearGroup.val_det_apply Q, hQdet, inv_one]
    have hQinv_e1 : (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ e1 = b := by
      calc (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ e1
          = (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ
              ((Q : Matrix (Fin 2) (Fin 2) K) *ᵥ b) := by rw [hQb]
        _ = ((((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
              (Q : Matrix (Fin 2) (Fin 2) K)) *ᵥ b := by rw [Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ b := by
              rw [show (((Q⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
                  (Q : Matrix (Fin 2) (Fin 2) K) = 1 by
                rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
        _ = b := by rw [Matrix.one_mulVec]
    have hQinv_mem : embSL Q⁻¹ ∈ H := hD (mem_levi_iff.mpr ⟨Q⁻¹, rfl⟩)
    have hb_mem : upperElem b ∈ H := by
      rw [← hQinv_e1, ← embSL_conj_upper Q⁻¹ hQinv_det e1]
      exact H.mul_mem (H.mul_mem hQinv_mem he1_mem) (H.inv_mem hQinv_mem)
    exact hb_mem

theorem lowerRadical_le_of_exists (H : Subgroup (SL(3, K))) (hD : levi ≤ H)
    (hex : ∃ c : Fin 2 → K, lowerElem c ∈ H ∧ lowerElem c ≠ 1) :
    lowerRadical ≤ H := by
  obtain ⟨c, hcH, hcne⟩ := hex
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hcne
    rw [hc0, lowerElem_zero]
  obtain ⟨Q, hQc, hQdet⟩ := exists_gl2_vecMul_inv_eq_e1 hc_ne
  have hQmem : embSL Q ∈ H := hD (mem_levi_iff.mpr ⟨Q, rfl⟩)
  have hQinv_mem : (embSL Q)⁻¹ ∈ H := H.inv_mem hQmem
  have he1_mem : lowerElem (Pi.single 0 (1 : K)) ∈ H := by
    rw [← hQc, ← embSL_conj_lower Q hQdet c]
    exact H.mul_mem (H.mul_mem hQmem hcH) hQinv_mem
  intro g hg
  rw [mem_lowerRadical_iff] at hg
  obtain ⟨c', rfl⟩ := hg
  by_cases hc'0 : c' = 0
  · rw [hc'0, lowerElem_zero]
    exact H.one_mem
  · obtain ⟨R, hRc', hRdet⟩ := exists_gl2_vecMul_inv_eq_e1 hc'0
    have hRinv_det : (((R⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_inv_det_apply R, Units.val_inv_eq_inv_val,
        Matrix.GeneralLinearGroup.val_det_apply R, hRdet, inv_one]
    have hrow : (R : Matrix (Fin 2) (Fin 2) K).row 0 = c' := by
      have hsingle : (Pi.single 0 (1 : K)) ᵥ* (R : Matrix (Fin 2) (Fin 2) K) =
          (R : Matrix (Fin 2) (Fin 2) K).row 0 := by
        rw [Matrix.single_vecMul]
        simp
      rw [← hsingle]
      calc (Pi.single 0 (1 : K)) ᵥ* (R : Matrix (Fin 2) (Fin 2) K)
          = (c' ᵥ* (((R⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) ᵥ*
              (R : Matrix (Fin 2) (Fin 2) K) := by rw [← hRc']
        _ = c' ᵥ* ((((R⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
              (R : Matrix (Fin 2) (Fin 2) K)) := by rw [Matrix.vecMul_vecMul]
        _ = c' ᵥ* (1 : Matrix (Fin 2) (Fin 2) K) := by
              rw [show (((R⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
                  (R : Matrix (Fin 2) (Fin 2) K) = 1 by
                rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
        _ = c' := by rw [Matrix.vecMul_one]
    have hRinv_mem : embSL R⁻¹ ∈ H := hD (mem_levi_iff.mpr ⟨R⁻¹, rfl⟩)
    have hc'_mem : lowerElem c' ∈ H := by
      rw [← hrow]
      have hrow_single : (R : Matrix (Fin 2) (Fin 2) K).row 0 =
          (Pi.single 0 (1 : K)) ᵥ* (R : Matrix (Fin 2) (Fin 2) K) := by
        rw [Matrix.single_vecMul]
        simp
      rw [hrow_single]
      rw [← embSL_inv_conj_lower R hRinv_det (Pi.single 0 (1 : K))]
      have hRinv_mem' : (embSL R)⁻¹ ∈ H := by
        rw [← map_inv]
        exact hRinv_mem
      exact H.mul_mem (H.mul_mem hRinv_mem' he1_mem) (H.inv_mem hRinv_mem')
    exact hc'_mem

private theorem upperRadical_transvection_zero_two (t : K) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t ∈ upperRadical := by
  rw [mem_upperRadical_iff]
  refine ⟨fun i => if i = 0 then t else 0, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperElem, blockMat, SpecialLinearGroup.transvection_coe, Matrix.single]

private theorem upperRadical_transvection_one_two (t : K) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t ∈ upperRadical := by
  rw [mem_upperRadical_iff]
  refine ⟨fun i => if i = 1 then t else 0, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperElem, blockMat, SpecialLinearGroup.transvection_coe, Matrix.single]

private theorem lowerRadical_transvection_two_zero (t : K) :
    SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t ∈ lowerRadical := by
  rw [mem_lowerRadical_iff]
  refine ⟨fun j => if j = 0 then t else 0, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerElem, blockMat, SpecialLinearGroup.transvection_coe, Matrix.single]

private theorem lowerRadical_transvection_two_one (t : K) :
    SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t ∈ lowerRadical := by
  rw [mem_lowerRadical_iff]
  refine ⟨fun j => if j = 1 then t else 0, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerElem, blockMat, SpecialLinearGroup.transvection_coe, Matrix.single]

@[expose] def SwapsRadicals (theta : SL(3, K) ≃* SL(3, K)) : Prop :=
  (∀ x : SL(3, K), x ∈ upperRadical ↔ theta x ∈ lowerRadical) ∧
    ∀ x : SL(3, K), x ∈ lowerRadical ↔ theta x ∈ upperRadical

theorem eq_levi_or_top_of_swaps_radicals (H : Subgroup (SL(3, K)))
    (theta : SL(3, K) ≃* SL(3, K)) (h2 : (2 : K) ≠ 0)
    (hD : levi ≤ H) (hH : H.map theta.toMonoidHom ≤ H)
    (hswap : SwapsRadicals theta) :
    H = levi ∨ H = ⊤ := by
  by_cases hEq : H = levi
  · exact Or.inl hEq
  · right
    have hnotle : ¬ H ≤ levi := by
      intro hle
      exact hEq (le_antisymm hle hD)
    have hex : ∃ g : SL(3, K), g ∈ H ∧ g ∉ levi := by
      by_contra h
      apply hnotle
      intro x hx
      by_contra hxlevi
      exact h ⟨x, hx, hxlevi⟩
    obtain ⟨g, hgH, hgD⟩ := hex
    have hres := exists_radical_of_not_le_levi H hD h2 hgH hgD
    have hupper : upperRadical ≤ H := by
      rcases hres with hup | hlow
      · exact upperRadical_le_of_exists H hD hup
      · have hlowle : lowerRadical ≤ H := lowerRadical_le_of_exists H hD hlow
        intro y hy
        have hpre : theta.symm y ∈ lowerRadical :=
          (hswap.2 (theta.symm y)).mpr (by simpa using hy)
        have hpreH : theta.symm y ∈ H := hlowle hpre
        have hmap : theta (theta.symm y) ∈ H :=
          hH (Subgroup.mem_map.mpr ⟨theta.symm y, hpreH, rfl⟩)
        simpa using hmap
    have hlower : lowerRadical ≤ H := by
      rcases hres with hup | hlow
      · have hupperle : upperRadical ≤ H := upperRadical_le_of_exists H hD hup
        intro y hy
        have hpre : theta.symm y ∈ upperRadical :=
          (hswap.1 (theta.symm y)).mpr (by simpa using hy)
        have hpreH : theta.symm y ∈ H := hupperle hpre
        have hmap : theta (theta.symm y) ∈ H :=
          hH (Subgroup.mem_map.mpr ⟨theta.symm y, hpreH, rfl⟩)
        simpa using hmap
      · exact lowerRadical_le_of_exists H hD hlow
    have hT : ∀ (i j : Fin 3) (hij : i ≠ j) (t : K),
        SpecialLinearGroup.transvection hij t ∈ H := by
      intro i j hij t
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hD (levi_transvection_zero_one t)
      · exact hupper (upperRadical_transvection_zero_two t)
      · exact hD (levi_transvection_one_zero t)
      · exact absurd rfl hij
      · exact hupper (upperRadical_transvection_one_two t)
      · exact hlower (lowerRadical_transvection_two_zero t)
      · exact hlower (lowerRadical_transvection_two_one t)
      · exact absurd rfl hij
    exact CFSG.LinearAlgebra.SLThreeRootGeneration.closure_transvections_eq_top H hT

@[expose] noncomputable def blockGL (P : GL (Fin 2) K) (s : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K))
    (by
      rw [blockMat_det_diag]
      exact mul_ne_zero P.det_ne_zero s.ne_zero)

@[simp] theorem blockGL_coe (P : GL (Fin 2) K) (s : Kˣ) :
    ((blockGL P s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K) :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem blockGL_inv (P : GL (Fin 2) K) (s : Kˣ) :
    (blockGL P s)⁻¹ = blockGL P⁻¹ s⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inv, blockGL_coe, blockGL_coe]
  have hprod : blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K) *
      blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 ((s⁻¹ : Kˣ) : K) = 1 := by
    rw [blockMat_mul, ← blockMat_one, blockMat_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (P : Matrix (Fin 2) (Fin 2) K) *
          (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
        Matrix.vecMulVec_zero, add_zero]
    · funext i; simp
    · funext j; simp
    · rw [zero_dotProduct, zero_add,
        show (s : K) * ((s⁻¹ : Kˣ) : K) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
  exact Matrix.inv_eq_right_inv hprod

private theorem blockMat_conj_upper_diag (P : GL (Fin 2) K) (s : Kˣ) (v : Fin 2 → K) :
    blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K) *
        blockMat 1 v 0 1 *
        blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 ((s⁻¹ : Kˣ) : K) =
      blockMat 1 (fun i => ((s⁻¹ : Kˣ) : K) * ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ v) i) 0 1 := by
  rw [blockMat_mul, blockMat_mul, blockMat_inj]
  have hPPinv : (P : Matrix (Fin 2) (Fin 2) K) *
      (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hssinv : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.vecMulVec_zero, hPPinv]
  · funext i
    simp [Pi.smul_apply, mul_comm]
  · funext j
    simp [Matrix.zero_vecMul, Matrix.vecMul_one, Matrix.vecMul, dotProduct,
      zero_dotProduct, Fin.sum_univ_two]
  · simpa [dotProduct_zero, hssinv]

private theorem blockMat_conj_lower_diag (P : GL (Fin 2) K) (s : Kˣ) (u : Fin 2 → K) :
    blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K) *
        blockMat 1 0 u 1 *
        blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 ((s⁻¹ : Kˣ) : K) =
      blockMat 1 0 (fun j => (s : K) * (u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) j) 1 := by
  rw [blockMat_mul, blockMat_mul, blockMat_inj]
  have hPPinv : (P : Matrix (Fin 2) (Fin 2) K) *
      (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hssinv : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.vecMulVec_zero, hPPinv]
  · funext i
    simp
  · funext j
    simp [Pi.smul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      mul_assoc, mul_comm, mul_left_comm]
    ring
  · simpa [dotProduct_zero, hssinv]

@[expose] noncomputable def graphAut (B : GL (Fin 3) K) : SL(3, K) ≃* SL(3, K) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K B *
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K

theorem coe_graphAut (B : GL (Fin 3) K) (g : SL(3, K)) :
    ((graphAut B g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) *
        ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))ᵀ) *
        (((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [graphAut, MulAut.mul_apply]
  change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K B
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K g) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    (B : Matrix (Fin 3) (Fin 3) K) *
      ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))ᵀ) *
      (((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
  have h := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation 3 K B
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K g))
  simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    Matrix.SpecialLinearGroup.coe_inv] using h

theorem graphAut_upper (P : GL (Fin 2) K) (s : Kˣ) (u : Fin 2 → K) :
    graphAut (blockGL P s) (upperElem u) =
      lowerElem (fun j => -((s : K) *
        (u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) j)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  rw [coe_graphAut, blockGL_coe, blockGL_inv, blockGL_coe, upperElem_inv]
  change blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K) *
      (blockMat 1 (-u) 0 1)ᵀ *
      blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 ((s⁻¹ : Kˣ) : K) =
    blockMat 1 0 (fun j => -((s : K) *
      (u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) j)) 1
  rw [blockMat_transpose, Matrix.transpose_one, blockMat_conj_lower_diag, blockMat_inj]
  refine ⟨rfl, rfl, ?_, rfl⟩
  funext j
  simp [Pi.smul_apply, Matrix.neg_vecMul, mul_neg, mul_comm]

theorem graphAut_lower (P : GL (Fin 2) K) (s : Kˣ) (u : Fin 2 → K) :
    graphAut (blockGL P s) (lowerElem u) =
      upperElem (fun i => -(((s⁻¹ : Kˣ) : K) *
        ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ u) i)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  rw [coe_graphAut, blockGL_coe, blockGL_inv, blockGL_coe, lowerElem_inv]
  change blockMat (P : Matrix (Fin 2) (Fin 2) K) 0 0 (s : K) *
      (blockMat 1 0 (-u) 1)ᵀ *
      blockMat (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 ((s⁻¹ : Kˣ) : K) =
    blockMat 1 (fun i => -(((s⁻¹ : Kˣ) : K) *
      ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ u) i)) 0 1
  rw [blockMat_transpose, Matrix.transpose_one, blockMat_conj_upper_diag, blockMat_inj]
  refine ⟨rfl, ?_, rfl, rfl⟩
  funext i
  simp [Pi.smul_apply, Matrix.mulVec_neg, mul_neg, mul_comm]

theorem graphAut_upper_surj (P : GL (Fin 2) K) (s : Kˣ) (c : Fin 2 → K) :
    ∃ u : Fin 2 → K, graphAut (blockGL P s) (upperElem u) = lowerElem c := by
  have hPPinv : (P : Matrix (Fin 2) (Fin 2) K) *
      (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hssinv : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let u : Fin 2 → K := (-(((s⁻¹ : Kˣ) : K) • c)) ᵥ*
    (P : Matrix (Fin 2) (Fin 2) K)
  refine ⟨u, ?_⟩
  rw [graphAut_upper]
  apply congrArg lowerElem
  have hu : u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      -(((s⁻¹ : Kˣ) : K) • c) := by
    calc u ᵥ* (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
        = ((-(((s⁻¹ : Kˣ) : K) • c)) ᵥ* (P : Matrix (Fin 2) (Fin 2) K)) ᵥ*
            (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := rfl
      _ = (-(((s⁻¹ : Kˣ) : K) • c)) ᵥ*
            ((P : Matrix (Fin 2) (Fin 2) K) *
              (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) := by
            rw [Matrix.vecMul_vecMul]
      _ = (-(((s⁻¹ : Kˣ) : K) • c)) ᵥ* (1 : Matrix (Fin 2) (Fin 2) K) := by rw [hPPinv]
      _ = -(((s⁻¹ : Kˣ) : K) • c) := by rw [Matrix.vecMul_one]
  rw [hu]
  funext j
  simp [Pi.smul_apply, Pi.neg_apply, mul_neg, neg_mul, mul_assoc]

theorem graphAut_lower_surj (P : GL (Fin 2) K) (s : Kˣ) (v : Fin 2 → K) :
    ∃ c : Fin 2 → K, graphAut (blockGL P s) (lowerElem c) = upperElem v := by
  have hPPinv : (P : Matrix (Fin 2) (Fin 2) K) *
      (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hssinv : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let c : Fin 2 → K := -((s : K) •
    ((((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v))
  refine ⟨c, ?_⟩
  rw [graphAut_lower]
  apply congrArg upperElem
  have hc : (P : Matrix (Fin 2) (Fin 2) K) *ᵥ c = -((s : K) • v) := by
    calc (P : Matrix (Fin 2) (Fin 2) K) *ᵥ c
        = (P : Matrix (Fin 2) (Fin 2) K) *ᵥ
            (-((s : K) • ((((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v))) := rfl
      _ = -((s : K) • ((P : Matrix (Fin 2) (Fin 2) K) *ᵥ
            ((((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ v))) := by
            rw [Matrix.mulVec_neg, Matrix.mulVec_smul]
      _ = -((s : K) • (((P : Matrix (Fin 2) (Fin 2) K) *
            (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) *ᵥ v)) := by
            rw [Matrix.mulVec_mulVec]
      _ = -((s : K) • ((1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) := by rw [hPPinv]
      _ = -((s : K) • v) := by rw [Matrix.one_mulVec]
  rw [hc]
  funext i
  fin_cases i <;>
    simp [Pi.smul_apply, mul_neg, neg_mul, mul_assoc, mul_comm] <;>
    ring

theorem graphAut_swaps (P : GL (Fin 2) K) (s : Kˣ) :
    SwapsRadicals (graphAut (blockGL P s)) := by
  constructor
  · intro x
    constructor
    · intro hx
      rw [mem_upperRadical_iff] at hx
      obtain ⟨u, rfl⟩ := hx
      rw [mem_lowerRadical_iff]
      exact ⟨_, graphAut_upper P s u⟩
    · intro hx
      rw [mem_lowerRadical_iff] at hx
      obtain ⟨c, hc⟩ := hx
      obtain ⟨u, hu⟩ := graphAut_upper_surj P s c
      have hxeq : graphAut (blockGL P s) x =
          graphAut (blockGL P s) (upperElem u) := by rw [hc, hu]
      rw [mem_upperRadical_iff]
      exact ⟨u, (graphAut (blockGL P s)).injective hxeq⟩
  · intro x
    constructor
    · intro hx
      rw [mem_lowerRadical_iff] at hx
      obtain ⟨u, rfl⟩ := hx
      rw [mem_upperRadical_iff]
      exact ⟨_, graphAut_lower P s u⟩
    · intro hx
      rw [mem_upperRadical_iff] at hx
      obtain ⟨v, hv⟩ := hx
      obtain ⟨c, hc⟩ := graphAut_lower_surj P s v
      have hxeq : graphAut (blockGL P s) x =
          graphAut (blockGL P s) (lowerElem c) := by rw [hv, hc]
      rw [mem_lowerRadical_iff]
      exact ⟨c, (graphAut (blockGL P s)).injective hxeq⟩

theorem eq_levi_or_top_of_graph_blockDiag (H : Subgroup (SL(3, K)))
    (P : GL (Fin 2) K) (s : Kˣ) (h2 : (2 : K) ≠ 0) (hD : levi ≤ H)
    (hH : H.map (graphAut (blockGL P s)).toMonoidHom ≤ H) :
    H = levi ∨ H = ⊤ :=
  eq_levi_or_top_of_swaps_radicals H (graphAut (blockGL P s)) h2 hD hH (graphAut_swaps P s)

end CFSG.LinearAlgebra.SLThreeLevi
