module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def sumEq7 : Fin 7 ≃ Fin 3 ⊕ Fin 4 where
  toFun i := if h : (i : ℕ) < 3 then Sum.inl ⟨i, h⟩ else Sum.inr ⟨(i : ℕ) - 3, by omega⟩
  invFun s := Sum.elim (fun a : Fin 3 => (⟨a, by omega⟩ : Fin 7))
    (fun b : Fin 4 => (⟨b + 3, by omega⟩ : Fin 7)) s
  left_inv i := by
    by_cases h : (i : ℕ) < 3
    · simp [h]
    · simp only [h, dite_false, Sum.elim_inr]
      ext
      simp only
      omega
  right_inv s := by
    rcases s with a | b
    · simp
    · simp only [Sum.elim_inr]
      split_ifs with h
      · exact absurd h (by omega)
      · rfl

theorem sumEq7_symm_inl_val (a : Fin 3) : ((sumEq7.symm (Sum.inl a) : Fin 7) : ℕ) = a := rfl

theorem sumEq7_symm_inr_val (b : Fin 4) : ((sumEq7.symm (Sum.inr b) : Fin 7) : ℕ) = b + 3 := rfl

@[expose] def D0 (K : Type) [Field K] : Matrix (Fin 7) (Fin 7) K :=
  Matrix.diagonal (fun i : Fin 7 => if (i : ℕ) < 3 then (1 : K) else 0)

@[expose] noncomputable def dagI {ι : Type} (h : UnitaryFieldData p f K) (M : Matrix ι ι K) :
    Matrix ι ι K :=
  (M.map h.bar)ᵀ

theorem dagI_mul {ι : Type} [Fintype ι] (h : UnitaryFieldData p f K) (M N : Matrix ι ι K) :
    dagI h (M * N) = dagI h N * dagI h M := by
  unfold dagI
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem dagI_dagI {ι : Type} (h : UnitaryFieldData p f K) (M : Matrix ι ι K) :
    dagI h (dagI h M) = M := by
  unfold dagI
  rw [Matrix.transpose_map, Matrix.map_map]
  simp [Function.comp_def, h.bar_bar]

theorem dagI_D0 (h : UnitaryFieldData p f K) : dagI h (D0 K) = D0 K := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [dagI, D0, Matrix.diagonal_apply]
  · simp [dagI, D0, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem dagI_submatrix {ι κ : Type} (h : UnitaryFieldData p f K) (M : Matrix ι ι K) (e : κ ≃ ι) :
    dagI h (M.submatrix e e) = (dagI h M).submatrix e e := by
  ext i j
  simp [dagI]

theorem blockDiag_mul {A A' : Matrix (Fin 3) (Fin 3) K} {B B' : Matrix (Fin 4) (Fin 4) K} :
    (Matrix.fromBlocks A 0 0 B).submatrix sumEq7 sumEq7 *
        (Matrix.fromBlocks A' 0 0 B').submatrix sumEq7 sumEq7 =
      (Matrix.fromBlocks (A * A') 0 0 (B * B')).submatrix sumEq7 sumEq7 := by
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem D0_eq_block : D0 K = (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) K) 0 0
    (0 : Matrix (Fin 4) (Fin 4) K)).submatrix sumEq7 sumEq7 := by
  have : (D0 K).submatrix sumEq7.symm sumEq7.symm =
      Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) K) 0 0 (0 : Matrix (Fin 4) (Fin 4) K) := by
    ext s t
    rcases s with a | a <;> rcases t with b | b <;>
      simp [D0, Matrix.diagonal_apply, Matrix.one_apply, sumEq7_symm_inl_val, sumEq7_symm_inr_val,
        Fin.ext_iff]
  rw [← this, Matrix.submatrix_submatrix]
  simp


theorem dagI_fromBlocks0 (h : UnitaryFieldData p f K) (A : Matrix (Fin 3) (Fin 3) K)
    (B : Matrix (Fin 4) (Fin 4) K) :
    dagI h (Matrix.fromBlocks A 0 0 B : Matrix (Fin 3 ⊕ Fin 4) (Fin 3 ⊕ Fin 4) K) =
      Matrix.fromBlocks (dagI h A) 0 0 (dagI h B) := by
  ext s t
  rcases s with a | a <;> rcases t with b | b <;> simp [dagI]

@[expose] noncomputable def barEq (h : UnitaryFieldData p f K) : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun y => ⟨h.bar y, h.bar_bar y⟩⟩

theorem barEq_apply (h : UnitaryFieldData p f K) (c : K) : barEq h c = h.bar c := rfl

theorem barEq_sq (h : UnitaryFieldData p f K) : barEq h ^ 2 = 1 := by
  apply RingEquiv.ext
  intro x
  rw [pow_two]
  exact h.bar_bar x

theorem barEq_ne_one (h : UnitaryFieldData p f K) : barEq h ≠ 1 := by
  intro heq
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  apply hc
  have := congrArg (fun φ : K ≃+* K => φ c) heq
  simpa [barEq_apply] using this

theorem conjTr_barEq (h : UnitaryFieldData p f K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    CFSG.LieType.Universal.Unitary.conjTr (barEq h) M = dagI h M := rfl

theorem exists_unitary_frame (h : UnitaryFieldData p f K) (e : Matrix (Fin 7) (Fin 7) K)
    (hdag : dagI h e = e) (A₀ : GL (Fin 7) K)
    (hA₀ : (A₀ : Matrix (Fin 7) (Fin 7) K) * e *
      ((A₀⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = D0 K) :
    ∃ R : GL (Fin 7) K, dagI h (R : Matrix (Fin 7) (Fin 7) K) * (R : Matrix (Fin 7) (Fin 7) K) = 1 ∧
      ((R⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * e * (R : Matrix (Fin 7) (Fin 7) K) =
        D0 K := by
  haveI : Finite K := h.finite
  set Mm : Matrix (Fin 7) (Fin 7) K := ((A₀⁻¹ : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) with hMm
  set Am : Matrix (Fin 7) (Fin 7) K := (A₀ : Matrix (Fin 7) (Fin 7) K) with hAm
  have hMA : Mm * Am = 1 := Units.inv_mul A₀
  have hAM : Am * Mm = 1 := Units.mul_inv A₀
  have hem : e * Mm = Mm * D0 K := by
    have h1 : Mm * (Am * e * Mm) = e * Mm := by
      have h2 : Mm * (Am * e * Mm) = (Mm * Am) * e * Mm := by simp only [Matrix.mul_assoc]
      rw [h2, hMA, Matrix.one_mul]
    calc e * Mm = Mm * (Am * e * Mm) := h1.symm
      _ = Mm * D0 K := by rw [hA₀]
  set G : Matrix (Fin 7) (Fin 7) K := dagI h Mm * Mm with hG
  have hcomm : D0 K * G = G * D0 K := by
    have h1 : D0 K * dagI h Mm = dagI h Mm * e := by
      have h2 := congrArg (dagI h) hem
      rw [dagI_mul, dagI_mul, hdag, dagI_D0] at h2
      exact h2.symm
    have hL : D0 K * G = dagI h Mm * e * Mm := by
      calc D0 K * G = (D0 K * dagI h Mm) * Mm := by rw [hG]; simp only [Matrix.mul_assoc]
        _ = (dagI h Mm * e) * Mm := by rw [h1]
        _ = dagI h Mm * e * Mm := rfl
    have hR : G * D0 K = dagI h Mm * e * Mm := by
      calc G * D0 K = dagI h Mm * (Mm * D0 K) := by rw [hG]; simp only [Matrix.mul_assoc]
        _ = dagI h Mm * (e * Mm) := by rw [hem]
        _ = dagI h Mm * e * Mm := by simp only [Matrix.mul_assoc]
    rw [hL, hR]
  have hGoff : ∀ i j : Fin 7, ((i : ℕ) < 3) ≠ ((j : ℕ) < 3) → G i j = 0 := by
    intro i j hij
    have hc := congrFun (congrFun hcomm i) j
    simp only [D0, Matrix.diagonal_mul, Matrix.mul_diagonal] at hc
    by_cases hi : (i : ℕ) < 3 <;> by_cases hj : (j : ℕ) < 3 <;> simp_all
  have hGherm : dagI h G = G := by
    rw [hG, dagI_mul, dagI_dagI]
  set G11 : Matrix (Fin 3) (Fin 3) K :=
    fun a b => G (sumEq7.symm (Sum.inl a)) (sumEq7.symm (Sum.inl b)) with hG11
  set G22 : Matrix (Fin 4) (Fin 4) K :=
    fun a b => G (sumEq7.symm (Sum.inr a)) (sumEq7.symm (Sum.inr b)) with hG22
  have hGs : G.submatrix sumEq7.symm sumEq7.symm = Matrix.fromBlocks G11 0 0 G22 := by
    ext s t
    rcases s with a | a <;> rcases t with b | b
    · rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Pi.zero_apply]
      exact hGoff _ _ (by simp [sumEq7_symm_inl_val, sumEq7_symm_inr_val])
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Pi.zero_apply]
      exact hGoff _ _ (by simp [sumEq7_symm_inl_val, sumEq7_symm_inr_val])
    · rfl
  have hGblk : G = (Matrix.fromBlocks G11 0 0 G22).submatrix sumEq7 sumEq7 := by
    rw [← hGs, Matrix.submatrix_submatrix]
    simp
  have hGX : G * (Am * dagI h Am) = 1 := by
    calc G * (Am * dagI h Am) = dagI h Mm * (Mm * Am) * dagI h Am := by
          rw [hG]; simp only [Matrix.mul_assoc]
      _ = dagI h Mm * dagI h Am := by rw [hMA, Matrix.mul_one]
      _ = dagI h (Am * Mm) := by rw [dagI_mul]
      _ = 1 := by rw [hAM]; unfold dagI; simp
  have hGdet : G.det ≠ 0 := by
    exact (Matrix.isUnit_det_of_right_inverse hGX).ne_zero
  have hdet_blk : G.det = G11.det * G22.det := by
    rw [hGblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have hdet11 : G11.det ≠ 0 := by
    intro h0
    apply hGdet
    rw [hdet_blk, h0, zero_mul]
  have hdet22 : G22.det ≠ 0 := by
    intro h0
    apply hGdet
    rw [hdet_blk, h0, mul_zero]
  have hG11h : dagI h G11 = G11 := by
    ext a b
    have hc := congrFun (congrFun hGherm (sumEq7.symm (Sum.inl b))) (sumEq7.symm (Sum.inl a))
    simp only [dagI, Matrix.transpose_apply, Matrix.map_apply] at hc
    show h.bar (G (sumEq7.symm (Sum.inl b)) (sumEq7.symm (Sum.inl a))) =
      G (sumEq7.symm (Sum.inl a)) (sumEq7.symm (Sum.inl b))
    rw [← hc, h.bar_bar]
  have hG22h : dagI h G22 = G22 := by
    ext a b
    have hc := congrFun (congrFun hGherm (sumEq7.symm (Sum.inr b))) (sumEq7.symm (Sum.inr a))
    simp only [dagI, Matrix.transpose_apply, Matrix.map_apply] at hc
    show h.bar (G (sumEq7.symm (Sum.inr b)) (sumEq7.symm (Sum.inr a))) =
      G (sumEq7.symm (Sum.inr a)) (sumEq7.symm (Sum.inr b))
    rw [← hc, h.bar_bar]
  have hσ2 := barEq_sq h
  have hσne := barEq_ne_one h
  have hu11 : IsUnit G11 := (Matrix.isUnit_iff_isUnit_det G11).mpr (isUnit_iff_ne_zero.mpr hdet11)
  have hu22 : IsUnit G22 := (Matrix.isUnit_iff_isUnit_det G22).mpr (isUnit_iff_ne_zero.mpr hdet22)
  obtain ⟨S1, hS1⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_matrix
    (barEq h) hσ2 hσne hu11.unit
    (by rw [IsUnit.unit_spec, conjTr_barEq, hG11h])
  obtain ⟨S2, hS2⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_matrix
    (barEq h) hσ2 hσne hu22.unit
    (by rw [IsUnit.unit_spec, conjTr_barEq, hG22h])
  rw [IsUnit.unit_spec, conjTr_barEq] at hS1
  rw [IsUnit.unit_spec, conjTr_barEq] at hS2
  set Bm : Matrix (Fin 7) (Fin 7) K :=
    (Matrix.fromBlocks (S1 : Matrix (Fin 3) (Fin 3) K) 0 0
      (S2 : Matrix (Fin 4) (Fin 4) K)).submatrix sumEq7 sumEq7 with hBm
  have hdetS1 : (S1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp S1.isUnit).ne_zero
  have hdetS2 : (S2 : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp S2.isUnit).ne_zero
  have hBdet : Bm.det ≠ 0 := by
    rw [hBm, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero hdetS1 hdetS2
  have hBu : IsUnit Bm := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hBdet)
  have hMu : IsUnit Mm := (A₀⁻¹ : GL (Fin 7) K).isUnit
  have hRu : IsUnit (Mm * Bm) := hMu.mul hBu
  have hdagBm : dagI h Bm = (Matrix.fromBlocks (dagI h (S1 : Matrix (Fin 3) (Fin 3) K)) 0 0
      (dagI h (S2 : Matrix (Fin 4) (Fin 4) K))).submatrix sumEq7 sumEq7 := by
    rw [hBm, dagI_submatrix, dagI_fromBlocks0]
  have key : dagI h Bm * G * Bm = 1 := by
    rw [hdagBm, hGblk, hBm, blockDiag_mul, blockDiag_mul, hS1, hS2, Matrix.fromBlocks_one,
      Matrix.submatrix_one_equiv]
  have hDB : D0 K * Bm = Bm * D0 K := by
    rw [D0_eq_block, hBm, blockDiag_mul, blockDiag_mul]
    simp
  refine ⟨hRu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    calc dagI h (Mm * Bm) * (Mm * Bm) = dagI h Bm * G * Bm := by
          rw [dagI_mul, hG]
          simp only [Matrix.mul_assoc]
      _ = 1 := key
  · rw [Matrix.coe_units_inv, IsUnit.unit_spec]
    have hRdet : IsUnit (Mm * Bm).det := (Matrix.isUnit_iff_isUnit_det _).mp hRu
    have hcommR : e * (Mm * Bm) = (Mm * Bm) * D0 K := by
      calc e * (Mm * Bm) = (e * Mm) * Bm := by rw [Matrix.mul_assoc]
        _ = (Mm * D0 K) * Bm := by rw [hem]
        _ = Mm * (D0 K * Bm) := by rw [Matrix.mul_assoc]
        _ = Mm * (Bm * D0 K) := by rw [hDB]
        _ = (Mm * Bm) * D0 K := by rw [Matrix.mul_assoc]
    rw [Matrix.mul_assoc, hcommR, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRdet,
      Matrix.one_mul]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
