module

public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix
open scoped CharTwo

variable {K : Type} [Field K] {n : ℕ}

namespace NonisotropicStabilizer

def basisMat (e f v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun k l => ![e, f, v] l k

def gramMat (lam : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 0; 0, 0, lam]

theorem colGram_apply (h : UnitaryFieldData 2 n K) (b : Fin 3 → Fin 3 → K) (i j : Fin 3) :
    (((Matrix.of fun k l => b l k).map h.bar)ᵀ * Matrix.of (fun k l => b l k)) i j =
      stdHermForm h 3 (b i) (b j) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, stdHermForm_apply]

theorem basisMat_conjTranspose_mul (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (he : stdHermForm h 3 e e = 0) (hf : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) (hev : stdHermForm h 3 e v = 0)
    (hfv : stdHermForm h 3 f v = 0) :
    ((basisMat e f v).map h.bar)ᵀ * basisMat e f v = gramMat (stdHermForm h 3 v v) := by
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    exact (by rwa [hef, map_one] at h' : (1 : K) = _).symm
  have hve : stdHermForm h 3 v e = 0 := by
    have h' := (stdHermForm_isSymm h 3).eq e v
    exact (by rwa [hev, map_zero] at h' : (0 : K) = _).symm
  have hvf : stdHermForm h 3 v f = 0 := by
    have h' := (stdHermForm_isSymm h 3).eq f v
    exact (by rwa [hfv, map_zero] at h' : (0 : K) = _).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMat, gramMat, colGram_apply, he, hf, hef, hfe, hev, hfv, hve, hvf]

theorem det_gramMat (h : UnitaryFieldData 2 n K) (lam : K) :
    (gramMat lam).det = lam := by
  haveI : CharP K 2 := h.charP
  rw [gramMat, Matrix.det_fin_three]
  simp [Matrix.of_apply]

theorem det_basisMat_ne_zero (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    (basisMat e f v).det ≠ 0 := by
  intro h0
  have hprod := congrArg Matrix.det (basisMat_conjTranspose_mul h he hf hef hev hfv)
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0,
    map_zero, zero_mul, det_gramMat h] at hprod
  exact hv hprod.symm

def upperLeft (D : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![D 0 0, D 0 1; D 1 0, D 1 1]

def blockDiag (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

def e2 : Fin 3 → K := Pi.single 2 1

theorem upperLeft_blockDiag (M : Matrix (Fin 2) (Fin 2) K) :
    upperLeft (blockDiag M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperLeft, blockDiag]

theorem blockDiag_mulVec_e2 (M : Matrix (Fin 2) (Fin 2) K) :
    blockDiag M *ᵥ e2 = e2 := by
  rw [blockDiag, e2, Matrix.mulVec_single_one]
  funext i
  fin_cases i <;> simp [Matrix.col_apply]

theorem det_blockDiag (M : Matrix (Fin 2) (Fin 2) K) :
    (blockDiag M).det = M.det := by
  rw [blockDiag, Matrix.det_fin_three, Matrix.det_fin_two]
  simp

theorem blockDiag_mul (M N : Matrix (Fin 2) (Fin 2) K) :
    blockDiag (M * N) = blockDiag M * blockDiag N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blockDiag_upperLeft {D : Matrix (Fin 3) (Fin 3) K} (h02 : D 0 2 = 0) (h12 : D 1 2 = 0)
    (h20 : D 2 0 = 0) (h21 : D 2 1 = 0) (h22 : D 2 2 = 1) :
    blockDiag (upperLeft D) = D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperLeft, blockDiag, h02, h12, h20, h21, h22]

theorem det_eq_det_upperLeft {D : Matrix (Fin 3) (Fin 3) K} (h02 : D 0 2 = 0) (h12 : D 1 2 = 0)
    (h20 : D 2 0 = 0) (h21 : D 2 1 = 0) (h22 : D 2 2 = 1) :
    D.det = (upperLeft D).det := by
  rw [Matrix.det_fin_three, upperLeft, Matrix.det_fin_two, h02, h12, h20, h21, h22]
  simp

def planeJ : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

def planeGram (lam : K) (N : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![N 0 0, N 0 1, 0; N 1 0, N 1 1, 0; 0, 0, lam]

theorem blockDiag_gramMat_mul (h : UnitaryFieldData 2 n K) (lam : K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    ((blockDiag M).map h.bar)ᵀ * gramMat lam * blockDiag M =
      planeGram lam ((M.map h.bar)ᵀ * planeJ * M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, planeGram, planeJ, gramMat, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockDiag_gramMat_eq (h : UnitaryFieldData 2 n K) {lam : K}
    {M : Matrix (Fin 2) (Fin 2) K} (hM : (M.map h.bar)ᵀ * planeJ * M = planeJ) :
    ((blockDiag M).map h.bar)ᵀ * gramMat lam * blockDiag M = gramMat lam := by
  rw [blockDiag_gramMat_mul, hM]
  rfl

theorem upperLeft_conjTranspose_gramMat (h : UnitaryFieldData 2 n K) (lam : K)
    {D : Matrix (Fin 3) (Fin 3) K} (h02 : D 0 2 = 0) (h12 : D 1 2 = 0)
    (h20 : D 2 0 = 0) (h21 : D 2 1 = 0) (h22 : D 2 2 = 1) :
    upperLeft ((D.map h.bar)ᵀ * gramMat lam * D) =
      ((upperLeft D).map h.bar)ᵀ * planeJ * upperLeft D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperLeft, planeJ, gramMat, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, Fin.sum_univ_two, h02, h12, h20, h21, h22]

theorem gram_apply_two (h : UnitaryFieldData 2 n K) (lam : K) {D : Matrix (Fin 3) (Fin 3) K}
    (h02 : D 0 2 = 0) (h12 : D 1 2 = 0) (h22 : D 2 2 = 1) (j : Fin 3) :
    ((D.map h.bar)ᵀ * gramMat lam * D) 2 j = lam * D 2 j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_three]
  have e0 : ((D.map h.bar)ᵀ) 2 0 = 0 := by simp [Matrix.transpose_apply, h02]
  have e1 : ((D.map h.bar)ᵀ) 2 1 = 0 := by simp [Matrix.transpose_apply, h12]
  have e2' : ((D.map h.bar)ᵀ) 2 2 = 1 := by simp [Matrix.transpose_apply, h22]
  rw [e0, e1, e2', zero_mul, zero_mul, one_mul]
  simp [gramMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem gramForm_conj (h : UnitaryFieldData 2 n K) {G : Matrix (Fin 3) (Fin 3) K}
    {P : Matrix (Fin 3) (Fin 3) K} (hG : (P.map h.bar)ᵀ * P = G) (x y : Fin 3 → K) :
    gramForm h 1 (P *ᵥ x) (P *ᵥ y) = gramForm h G x y := by
  rw [gramForm_mulVec, Matrix.mul_one, hG]

theorem mulVec_conj_inv (P : GL (Fin 3) K) (x : Fin 3 → K) :
    (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv_conj (P : GL (Fin 3) K) (x : Fin 3 → K) :
    ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_conj_three (P : GL (Fin 3) K) (A : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K) :
    (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x))) =
      A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x) := by
  rw [show (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x))) =
      ((P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
        (A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x)) from
      Matrix.mulVec_mulVec (A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ x)) _
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)]
  rw [show (P : Matrix (Fin 3) (Fin 3) K) *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
    Matrix.one_mulVec]

theorem conj_mem_gramSU_one (h : UnitaryFieldData 2 n K) {G : Matrix (Fin 3) (Fin 3) K}
    {P : GL (Fin 3) K} (hG : ((P : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * P = G)
    {D : GL (Fin 3) K} (hD : D ∈ gramSU h G) : (P * D * P⁻¹) ∈ gramSU h 1 := by
  rw [mem_gramSU_iff_isometry] at hD ⊢
  obtain ⟨hDiso, hDdet⟩ := hD
  let Pm : Matrix (Fin 3) (Fin 3) K := P
  let Pi : Matrix (Fin 3) (Fin 3) K := (P⁻¹ : GL (Fin 3) K)
  let Dm : Matrix (Fin 3) (Fin 3) K := D
  have hPPi : Pm * Pi = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcoe : ((P * D * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Pm * Dm * Pi := by
    rw [Units.val_mul, Units.val_mul]
  refine ⟨fun x y => ?_, ?_⟩
  · have hx : (Pm * Dm * Pi) *ᵥ x = Pm *ᵥ (Dm *ᵥ (Pi *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hy : (Pm * Dm * Pi) *ᵥ y = Pm *ᵥ (Dm *ᵥ (Pi *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hcoe, hx, hy, gramForm_conj h hG, hDiso]
    rw [← gramForm_conj h hG (Pi *ᵥ x) (Pi *ᵥ y), mulVec_conj_inv P x, mulVec_conj_inv P y]
  · rw [hcoe, Matrix.det_mul, Matrix.det_mul, hDdet, mul_one]
    have hdet : Pm.det * Pi.det = 1 := by
      have h := congrArg Matrix.det hPPi
      rwa [Matrix.det_mul, Matrix.det_one] at h
    exact hdet

theorem conj_inv_mem_gramSU (h : UnitaryFieldData 2 n K) {G : Matrix (Fin 3) (Fin 3) K}
    {P : GL (Fin 3) K} (hG : ((P : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * P = G)
    {g : GL (Fin 3) K} (hg : g ∈ gramSU h 1) : (P⁻¹ * g * P) ∈ gramSU h G := by
  rw [mem_gramSU_iff_isometry] at hg ⊢
  obtain ⟨hgIso, hgdet⟩ := hg
  let Pm : Matrix (Fin 3) (Fin 3) K := P
  let Pi : Matrix (Fin 3) (Fin 3) K := (P⁻¹ : GL (Fin 3) K)
  let gm : Matrix (Fin 3) (Fin 3) K := g
  have hPPi : Pm * Pi = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcoe : ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Pi * gm * Pm := by
    rw [Units.val_mul, Units.val_mul]
  refine ⟨fun x y => ?_, ?_⟩
  · have hx : (Pi * gm * Pm) *ᵥ x = Pi *ᵥ (gm *ᵥ (Pm *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hy : (Pi * gm * Pm) *ᵥ y = Pi *ᵥ (gm *ᵥ (Pm *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hcoe, hx, hy]
    calc gramForm h G (Pi *ᵥ (gm *ᵥ (Pm *ᵥ x))) (Pi *ᵥ (gm *ᵥ (Pm *ᵥ y)))
        = gramForm h 1 (Pm *ᵥ (Pi *ᵥ (gm *ᵥ (Pm *ᵥ x))))
            (Pm *ᵥ (Pi *ᵥ (gm *ᵥ (Pm *ᵥ y)))) := (gramForm_conj h hG _ _).symm
      _ = gramForm h 1 (gm *ᵥ (Pm *ᵥ x)) (gm *ᵥ (Pm *ᵥ y)) := by
            rw [mulVec_conj_three P gm x, mulVec_conj_three P gm y]
      _ = gramForm h 1 (Pm *ᵥ x) (Pm *ᵥ y) := hgIso _ _
      _ = gramForm h G x y := gramForm_conj h hG x y
  · rw [hcoe, Matrix.det_mul, Matrix.det_mul, hgdet, mul_one]
    have hdet : Pi.det * Pm.det = 1 := by
      have h := congrArg Matrix.det hPPi
      rw [Matrix.det_mul, Matrix.det_one] at h
      simpa [mul_comm] using h
    exact hdet

noncomputable def basisGL (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (basisMat e f v)
    (det_basisMat_ne_zero h hv he hf hef hev hfv)

theorem basisGL_coe (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    (basisGL h hv he hf hef hev hfv : Matrix (Fin 3) (Fin 3) K) = basisMat e f v := by
  simp [basisGL]

theorem basisGL_mulVec_e2 (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    (basisGL h hv he hf hef hev hfv : Matrix (Fin 3) (Fin 3) K) *ᵥ e2 = v := by
  rw [basisGL_coe, basisMat, e2, Matrix.mulVec_single_one]
  funext i
  fin_cases i <;> simp [Matrix.col_apply]

theorem inv_mulVec_eq_of_mulVec_eq (P : GL (Fin 3) K) {x y : Fin 3 → K}
    (h : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ x = y) :
    ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y = x := by
  rw [← h]
  exact mulVec_inv_conj P x

theorem basisGL_inv_mulVec (h : UnitaryFieldData 2 n K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    ((basisGL h hv he hf hef hev hfv)⁻¹ : GL (Fin 3) K) *ᵥ v = e2 :=
  inv_mulVec_eq_of_mulVec_eq _ (basisGL_mulVec_e2 h hv he hf hef hev hfv)

noncomputable def blockDiagGL (M : GL (Fin 2) K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blockDiag (M : Matrix (Fin 2) (Fin 2) K))
    (by rw [det_blockDiag]; exact M.det_ne_zero)

theorem coe_blockDiagGL (M : GL (Fin 2) K) :
    (blockDiagGL M : Matrix (Fin 3) (Fin 3) K) = blockDiag (M : Matrix (Fin 2) (Fin 2) K) := by
  simp [blockDiagGL]

noncomputable def blockDiagHom : GL (Fin 2) K →* GL (Fin 3) K where
  toFun := blockDiagGL
  map_one' := by
    apply Units.ext
    rw [coe_blockDiagGL, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockDiag]
  map_mul' := by
    intro M N
    apply Units.ext
    simp only [coe_blockDiagGL, Units.val_mul, blockDiag_mul]

noncomputable def conjBlockHom (P : GL (Fin 3) K) : GL (Fin 2) K →* GL (Fin 3) K :=
  (MulAut.conj P).toMonoidHom.comp blockDiagHom

theorem conjBlockHom_apply (P : GL (Fin 3) K) (M : GL (Fin 2) K) :
    conjBlockHom P M = P * blockDiagGL M * P⁻¹ := by
  change MulAut.conj P (blockDiagHom M) = P * blockDiagGL M * P⁻¹
  rw [MulAut.conj_apply]
  rfl

theorem mulVec_conj (P D : GL (Fin 3) K) (x : Fin 3 → K) :
    ((P * D * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((D : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x)) := by
  let Pm : Matrix (Fin 3) (Fin 3) K := P
  let Dm : Matrix (Fin 3) (Fin 3) K := D
  let Pi : Matrix (Fin 3) (Fin 3) K := (P⁻¹ : GL (Fin 3) K)
  have hcoe : ((P * D * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Pm * Dm * Pi := by
    rw [Units.val_mul, Units.val_mul]
  rw [hcoe]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem blockDiagGL_mem_gramSU (h : UnitaryFieldData 2 n K) {lam : K}
    {M : gramSU h planeJ} :
    blockDiagGL (M : GL (Fin 2) K) ∈ gramSU h (gramMat lam) := by
  obtain ⟨hJ, hdet⟩ := mem_gramSU.mp M.2
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [coe_blockDiagGL]
    exact blockDiag_gramMat_eq h hJ
  · rw [coe_blockDiagGL, det_blockDiag, hdet]

theorem upperLeft_mem_gramSU_planeJ (h : UnitaryFieldData 2 n K) {lam : K} (hlam : lam ≠ 0)
    {D : GL (Fin 3) K} (hD : D ∈ gramSU h (gramMat lam))
    (hDv : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ e2 = e2) :
    (upperLeft (D : Matrix (Fin 3) (Fin 3) K)).det = 1 ∧
      ((upperLeft (D : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ * planeJ *
        upperLeft (D : Matrix (Fin 3) (Fin 3) K) = planeJ ∧
      blockDiag (upperLeft (D : Matrix (Fin 3) (Fin 3) K)) =
        (D : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_gramSU] at hD
  obtain ⟨hDgram, hDdet⟩ := hD
  have h02 : (D : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    have h := congrFun hDv 0
    rw [e2, Matrix.mulVec_single_one] at h
    simpa using h
  have h12 : (D : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have h := congrFun hDv 1
    rw [e2, Matrix.mulVec_single_one] at h
    simpa using h
  have h22 : (D : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := congrFun hDv 2
    rw [e2, Matrix.mulVec_single_one] at h
    simpa using h
  have h20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have hh := congrFun (congrFun hDgram 2) 0
    rw [gram_apply_two (D := (D : Matrix (Fin 3) (Fin 3) K)) h lam h02 h12 h22 0,
      show gramMat lam 2 0 = 0 from by simp [gramMat]] at hh
    exact (mul_eq_zero.mp hh).resolve_left hlam
  have h21 : (D : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have hh := congrFun (congrFun hDgram 2) 1
    rw [gram_apply_two (D := (D : Matrix (Fin 3) (Fin 3) K)) h lam h02 h12 h22 1,
      show gramMat lam 2 1 = 0 from by simp [gramMat]] at hh
    exact (mul_eq_zero.mp hh).resolve_left hlam
  have hUL := upperLeft_conjTranspose_gramMat h lam h02 h12 h20 h21 h22
  have hG' : upperLeft (gramMat lam) = planeJ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperLeft, gramMat, planeJ]
  refine ⟨?_, ?_, blockDiag_upperLeft h02 h12 h20 h21 h22⟩
  · rw [det_eq_det_upperLeft h02 h12 h20 h21 h22] at hDdet
    exact hDdet
  · have h := congrArg upperLeft hDgram
    rw [hUL, hG'] at h
    exact h

end NonisotropicStabilizer

theorem nonempty_gramSU_mulEquiv_sesq (h : UnitaryFieldData 2 n K)
    (G : Matrix (Fin 2) (Fin 2) K) :
    Nonempty (gramSU h G ≃* sesqSpecialUnitaryGroup (gramForm h G)) := by
  let Ψ := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := K)
  have hEq : (gramSU h G).map Ψ.toMonoidHom = sesqSpecialUnitaryGroup (gramForm h G) := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (toLin_mem_sesqSpecialUnitaryGroup_iff h G M).mpr hM
    · intro hg
      exact ⟨Ψ.symm g, (toLin_mem_sesqSpecialUnitaryGroup_iff h G _).mp (by
        rwa [MulEquiv.apply_symm_apply]), Ψ.apply_symm_apply g⟩
  exact ⟨(Ψ.subgroupMap (gramSU h G)).trans (MulEquiv.subgroupCongr hEq)⟩

open NonisotropicStabilizer in
theorem isL2_of_forall_mem_iff_mulVec_eq {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    {L : Subgroup (StatedSU 3 (2 ^ n) K)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v) :
    IsL2 L n := by
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  classical
  let P : GL (Fin 3) K := basisGL h hv he hf hef hev hfv
  have hPG : ((P : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * P =
      gramMat (stdHermForm h 3 v v) := by
    rw [show (P : Matrix (Fin 3) (Fin 3) K) = basisMat e f v from
      basisGL_coe h hv he hf hef hev hfv]
    exact basisMat_conjTranspose_mul h he hf hef hev hfv
  have hPv : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ e2 = v :=
    basisGL_mulVec_e2 h hv he hf hef hev hfv
  have hPinv : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = e2 :=
    basisGL_inv_mulVec h hv he hf hef hev hfv
  have hLmem : ∀ g : L,
      ((g : L) : GL (Fin 3) K) ∈ gramSU h (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro g
    have hg : ((g : L) : GL (Fin 3) K) ∈ StatedSU 3 (2 ^ n) K :=
      ((g : L) : StatedSU 3 (2 ^ n) K).2
    change ((g : L) : GL (Fin 3) K) ∈ unitarySU 2 n K 3 at hg
    rwa [unitarySU_eq_gramSU] at hg
  let φ : gramSU h planeJ →* StatedSU 3 (2 ^ n) K :=
    ((conjBlockHom P).comp (gramSU h planeJ).subtype).codRestrict _
      (fun M => by
        change conjBlockHom P (M : GL (Fin 2) K) ∈ unitarySU 2 n K 3
        rw [conjBlockHom_apply, unitarySU_eq_gramSU]
        exact conj_mem_gramSU_one h hPG (blockDiagGL_mem_gramSU h (M := M)))
  have hφcoe : ∀ M : gramSU h planeJ,
      ((φ M : StatedSU 3 (2 ^ n) K) : GL (Fin 3) K) = conjBlockHom P (M : GL (Fin 2) K) :=
    fun M => rfl
  let ψ : gramSU h planeJ →* L :=
    φ.codRestrict L (fun M => by
      refine (hL (φ M)).mpr ?_
      rw [hφcoe, conjBlockHom_apply, mulVec_conj, hPinv, coe_blockDiagGL, blockDiag_mulVec_e2,
        hPv])
  have hψcoe : ∀ M : gramSU h planeJ,
      ((ψ M : L) : GL (Fin 3) K) = conjBlockHom P (M : GL (Fin 2) K) :=
    fun M => rfl
  have hsurj : Function.Surjective ψ := by
    intro g
    let D : GL (Fin 3) K := P⁻¹ * ((g : L) : GL (Fin 3) K) * P
    have hDmem : D ∈ gramSU h (gramMat (stdHermForm h 3 v v)) :=
      conj_inv_mem_gramSU h hPG (hLmem g)
    have hDv : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ e2 = e2 := by
      have hcoe : (D : Matrix (Fin 3) (Fin 3) K) =
          ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((g : L) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (P : Matrix (Fin 3) (Fin 3) K) := by
        rw [Units.val_mul, Units.val_mul]
      rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv, (hL g).mp g.2, hPinv]
    have hUL := upperLeft_mem_gramSU_planeJ h hv hDmem hDv
    let MGL : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (upperLeft (D : Matrix (Fin 3) (Fin 3) K))
        (by rw [hUL.1]; exact one_ne_zero)
    have hMGL : (MGL : Matrix (Fin 2) (Fin 2) K) =
        upperLeft (D : Matrix (Fin 3) (Fin 3) K) := by
      simp [MGL]
    let M : gramSU h planeJ :=
      ⟨MGL, by rw [hMGL]; exact hUL.2.1, by rw [hMGL]; exact hUL.1⟩
    refine ⟨M, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h1 : blockDiagGL MGL = D := by
      apply Units.ext
      rw [coe_blockDiagGL, hMGL]
      exact hUL.2.2
    have h2 : conjBlockHom P MGL = ((g : L) : GL (Fin 3) K) := by
      rw [conjBlockHom_apply, h1]
      show P * (P⁻¹ * ((g : L) : GL (Fin 3) K) * P) * P⁻¹ = ((g : L) : GL (Fin 3) K)
      group
    rw [hψcoe]
    simpa using h2
  have hinj : Function.Injective ψ := by
    intro M N hMN
    have hGL : conjBlockHom P (M : GL (Fin 2) K) = conjBlockHom P (N : GL (Fin 2) K) := by
      rw [← hψcoe M, ← hψcoe N]
      exact congrArg (fun x : L => ((x : L) : GL (Fin 3) K)) hMN
    rw [conjBlockHom_apply, conjBlockHom_apply] at hGL
    have hBD : blockDiagGL (M : GL (Fin 2) K) = blockDiagGL (N : GL (Fin 2) K) := by
      calc blockDiagGL (M : GL (Fin 2) K)
          = P⁻¹ * (P * blockDiagGL (M : GL (Fin 2) K) * P⁻¹) * P := by group
        _ = P⁻¹ * (P * blockDiagGL (N : GL (Fin 2) K) * P⁻¹) * P := by rw [hGL]
        _ = blockDiagGL (N : GL (Fin 2) K) := by group
    have hmat : (((M : gramSU h planeJ) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (((N : gramSU h planeJ) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      have h := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hBD
      rw [coe_blockDiagGL, coe_blockDiagGL] at h
      have h' := congrArg upperLeft h
      rwa [upperLeft_blockDiag, upperLeft_blockDiag] at h'
    exact Subtype.ext (Units.ext hmat)
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  have hJsymm : (planeJ.map h.bar)ᵀ = planeJ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeJ]
  have hJdet : (planeJ (K := K)).det ≠ 0 := by
    rw [planeJ, Matrix.det_fin_two]
    simp
  obtain ⟨eG⟩ := nonempty_gramSU_mulEquiv_sesq h planeJ
  obtain ⟨eS⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2
    (h := h) (B := gramForm h planeJ) (gramForm_isSymm h hJsymm)
    (gramForm_separatingLeft h hJdet) (by simp)
  exact KTabD.isL2_of_mulEquiv_sl2 hn h.card_fixedField
    ((MulEquiv.ofBijective ψ hbij).symm.trans (eG.trans eS))

end CFSG.ClassicalGroups.UnitaryFlag

end
