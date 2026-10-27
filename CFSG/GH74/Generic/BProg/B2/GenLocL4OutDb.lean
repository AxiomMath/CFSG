module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutTrans
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAsm
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutPlane

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section Blocks

variable {F : Type} [Field F]

@[expose] def bd2 (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

@[expose] def Gt : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

@[expose] def Gs : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

theorem bd2_mul (A B A' B' : Matrix (Fin 2) (Fin 2) F) : bd2 A B * bd2 A' B' = bd2 (A * A') (B * B') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem bd2_one : bd2 (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2]

theorem bd2_Gt : bd2 (1 : Matrix (Fin 2) (Fin 2) F) (-1) = Gt := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2, Gt]

theorem bd2_Gs : bd2 (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) !![1, 0; 0, -1] = Gs := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2, Gs]

theorem bd2_det (A B : Matrix (Fin 2) (Fin 2) F) : (bd2 A B).det = A.det * B.det := by
  simp only [bd2, Matrix.det_fin_two]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem bd2_inj {A B A' B' : Matrix (Fin 2) (Fin 2) F} (h : bd2 A B = bd2 A' B') : A = A' ∧ B = B' := by
  have e : ∀ i j, bd2 A B i j = bd2 A' B' i j := fun i j => by rw [h]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [bd2] using e 0 0
    · simpa [bd2] using e 0 1
    · simpa [bd2] using e 1 0
    · simpa [bd2] using e 1 1
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [bd2] using e 2 2
    · simpa [bd2] using e 2 3
    · simpa [bd2] using e 3 2
    · simpa [bd2] using e 3 3

theorem eq_bd2 (M : Matrix (Fin 4) (Fin 4) F) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0) (h12 : M 1 2 = 0) (h13 : M 1 3 = 0)
    (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) (h21 : M 2 1 = 0) (h31 : M 3 1 = 0) :
    M = bd2 !![M 0 0, M 0 1; M 1 0, M 1 1] !![M 2 2, M 2 3; M 3 2, M 3 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2, h02, h03, h12, h13, h20, h30, h21, h31]

theorem bd2_neg (A B : Matrix (Fin 2) (Fin 2) F) : bd2 (-A) (-B) = -(bd2 A B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2]

theorem Gt_comm_bd2 (A B : Matrix (Fin 2) (Fin 2) F) : Gt * bd2 A B = bd2 A B * Gt := by
  rw [← bd2_Gt, bd2_mul, bd2_mul]
  simp

theorem det_nonscalar_involution (h2 : (2 : F) ≠ 0) (H : Matrix (Fin 2) (Fin 2) F) (hH : H * H = 1) (h1 : H ≠ 1)
    (hm1 : H ≠ -1) : H.det = -1 := by
  obtain ⟨Q, hQ⟩ := inv2_diag h2 H hH h1 hm1
  have hd := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fin_two_of] at hd
  have hQ0 : (Q : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit).ne_zero
  have : (H.det + 1) * (Q : Matrix (Fin 2) (Fin 2) F).det = 0 := by linear_combination hd
  have := (mul_eq_zero.1 this).resolve_right hQ0
  linear_combination this

end Blocks

section JointFrame

variable {F : Type} [Field F]

theorem joint_frame [Finite F] (hF4 : Nat.card F % 4 = 3) (g h : Matrix (Fin 4) (Fin 4) F) (hgg : g * g = 1)
    (hhh : h * h = 1) (hgh : g * h = h * g) (hgdet : g.det = 1) (hhdet : h.det = 1) (hg1 : g ≠ 1) (hgm1 : g ≠ -1)
    (hh1 : h ≠ 1) (hhm1 : h ≠ -1) (hhg : h ≠ g) (hhmg : h ≠ -g) :
    ∃ P : GL (Fin 4) F, g * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Gt ∧
      h * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Gs := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨P0, hP0⟩ := CFSG.ComponentClassification.CatFactsL4U4.TBlocks.exists_frame_t2_L4 h2 hgg hgdet hg1 hgm1
  have hGt : (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] : Matrix (Fin 4) (Fin 4) F) = Gt := rfl
  rw [CFSG.GH74.Generic.BProg.B2.GenLocL4Out.X1_one, hGt] at hP0
  set Pm : Matrix (Fin 4) (Fin 4) F := (P0 : Matrix (Fin 4) (Fin 4) F) with hPm
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P0⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPP : Pm * Pi = 1 := coe_mul_inv P0
  have hPiP : Pi * Pm = 1 := coe_inv_mul P0
  have hg_eq : g = Pm * Gt * Pi := by
    calc g = g * (Pm * Pi) := by rw [hPP, Matrix.mul_one]
      _ = (g * Pm) * Pi := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hP0]
  set h' : Matrix (Fin 4) (Fin 4) F := Pi * h * Pm with hh'
  have hh_eq : h = Pm * h' * Pi := by
    calc h = (Pm * Pi) * h * (Pm * Pi) := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [hh']; simp only [Matrix.mul_assoc]
  have hGt_eq : Gt = Pi * g * Pm := by
    rw [hg_eq]
    calc Gt = (Pi * Pm) * Gt * (Pi * Pm) := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hcomm : Gt * h' = h' * Gt := by
    calc Gt * h' = Pi * (g * h) * Pm := by
          rw [hh', hGt_eq]
          calc Pi * g * Pm * (Pi * h * Pm) = Pi * g * (Pm * Pi) * h * Pm := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Pi * (h * g) * Pm := by rw [hgh]
      _ = h' * Gt := by
          rw [hh', hGt_eq]
          calc Pi * (h * g) * Pm = Pi * h * (Pm * Pi) * g * Pm := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
  have hGt0 : (Gt : Matrix (Fin 4) (Fin 4) F) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := rfl
  obtain ⟨b02, b03, b12, b13, b20, b30, b21, b31⟩ := blocks_vanish Gt h' h2 hGt0 hcomm
  have hh'bd := eq_bd2 h' b02 b03 b12 b13 b20 b30 b21 b31
  set H1 : Matrix (Fin 2) (Fin 2) F := !![h' 0 0, h' 0 1; h' 1 0, h' 1 1] with hH1
  set H2 : Matrix (Fin 2) (Fin 2) F := !![h' 2 2, h' 2 3; h' 3 2, h' 3 3] with hH2
  have hh'2 : h' * h' = 1 := by
    calc h' * h' = Pi * (h * h) * Pm := by
          rw [hh']
          calc Pi * h * Pm * (Pi * h * Pm) = Pi * h * (Pm * Pi) * h * Pm := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hhh, Matrix.mul_one, hPiP]
  have hsq : bd2 (H1 * H1) (H2 * H2) = bd2 1 1 := by
    rw [← bd2_mul, ← hh'bd, hh'2, bd2_one]
  obtain ⟨hH1sq, hH2sq⟩ := bd2_inj hsq
  have hdet' : H1.det * H2.det = 1 := by
    rw [← bd2_det, ← hh'bd]
    have : h'.det = h.det := by
      rw [hh', Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hPP, Matrix.det_one, one_mul]
    rw [this, hhdet]
  have hdet_scalar : ∀ H : Matrix (Fin 2) (Fin 2) F, (H = 1 ∨ H = -1) → H.det = 1 := by
    rintro H (rfl | rfl) <;> simp [Matrix.det_fin_two]
  have hm1ne : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  by_cases e1 : H1 = 1 ∨ H1 = -1
  · by_cases e2 : H2 = 1 ∨ H2 = -1
    · exfalso
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · apply hh1
        rw [hh_eq, hh'bd, e1, e2, bd2_one, Matrix.mul_one, hPP]
      · apply hhg
        rw [hh_eq, hh'bd, e1, e2, bd2_Gt]
        exact hg_eq.symm
      · apply hhmg
        have : bd2 (-1 : Matrix (Fin 2) (Fin 2) F) 1 = -Gt := by
          rw [← bd2_Gt, ← bd2_neg]; simp
        rw [hh_eq, hh'bd, e1, e2, this, hg_eq]
        simp only [Matrix.mul_neg, Matrix.neg_mul]
      · apply hhm1
        have : bd2 (-1 : Matrix (Fin 2) (Fin 2) F) (-1) = -1 := by
          rw [← bd2_one, ← bd2_neg]
        rw [hh_eq, hh'bd, e1, e2, this]
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, hPP]
    · exfalso
      push Not at e2
      have hd2 := det_nonscalar_involution h2 H2 hH2sq e2.1 e2.2
      have hd1 := hdet_scalar H1 e1
      rw [hd1, hd2] at hdet'
      exact hm1ne (by linear_combination hdet')
  · by_cases e2 : H2 = 1 ∨ H2 = -1
    · exfalso
      push Not at e1
      have hd1 := det_nonscalar_involution h2 H1 hH1sq e1.1 e1.2
      have hd2 := hdet_scalar H2 e2
      rw [hd1, hd2] at hdet'
      exact hm1ne (by linear_combination hdet')
    · push Not at e1 e2
      obtain ⟨Q1, hQ1⟩ := inv2_diag h2 H1 hH1sq e1.1 e1.2
      obtain ⟨Q2, hQ2⟩ := inv2_diag h2 H2 hH2sq e2.1 e2.2
      have hQ1d : (Q1 : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q1.isUnit).ne_zero
      have hQ2d : (Q2 : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q2.isUnit).ne_zero
      set Qm : Matrix (Fin 4) (Fin 4) F := bd2 (Q1 : Matrix (Fin 2) (Fin 2) F) (Q2 : Matrix (Fin 2) (Fin 2) F) with hQm
      have hQmdet : Qm.det ≠ 0 := by rw [hQm, bd2_det]; exact mul_ne_zero hQ1d hQ2d
      refine ⟨P0 * Matrix.GeneralLinearGroup.mkOfDetNeZero Qm hQmdet, ?_, ?_⟩
      · show g * (Pm * Qm) = (Pm * Qm) * Gt
        rw [← Matrix.mul_assoc, hP0, Matrix.mul_assoc, Matrix.mul_assoc, hQm, Gt_comm_bd2]
      · show h * (Pm * Qm) = (Pm * Qm) * Gs
        have hhP : h * Pm = Pm * h' := by
          rw [hh_eq]
          simp only [Matrix.mul_assoc]
          rw [hPiP, Matrix.mul_one]
        rw [← Matrix.mul_assoc, hhP, Matrix.mul_assoc, hh'bd, hQm, bd2_mul, hQ1, hQ2, ← bd2_Gs, Matrix.mul_assoc, bd2_mul]

end JointFrame

section DbFrame

variable {F : Type} [Field F]

theorem comm_of_frame {P : GL (Fin 4) F} {g G B : Matrix (Fin 4) (Fin 4) F}
    (hP : g * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * G) (hGt : Gᵀ = G)
    (hgB : g * B = B * gᵀ) :
    G * (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) =
      (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) * G := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hGPi : Pi * g = G * Pi := by
    calc Pi * g = Pi * g * (Pm * Pi) := by rw [hPP, Matrix.mul_one]
      _ = Pi * (g * Pm) * Pi := by simp only [Matrix.mul_assoc]
      _ = (Pi * Pm) * G * Pi := by rw [hP]; simp only [Matrix.mul_assoc]
      _ = G * Pi := by rw [hPiP, Matrix.one_mul]
  have hGPi' : gᵀ * Piᵀ = Piᵀ * G := by
    have := congrArg Matrix.transpose hGPi
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hGt] at this
    exact this
  calc G * (Pi * B * Piᵀ) = (G * Pi) * B * Piᵀ := by simp only [Matrix.mul_assoc]
    _ = (Pi * g) * B * Piᵀ := by rw [hGPi]
    _ = Pi * (g * B) * Piᵀ := by simp only [Matrix.mul_assoc]
    _ = Pi * (B * gᵀ) * Piᵀ := by rw [hgB]
    _ = Pi * B * (gᵀ * Piᵀ) := by simp only [Matrix.mul_assoc]
    _ = Pi * B * (Piᵀ * G) := by rw [hGPi']
    _ = (Pi * B * Piᵀ) * G := by simp only [Matrix.mul_assoc]

theorem diag_of_comm (h2 : (2 : F) ≠ 0) (D : Matrix (Fin 4) (Fin 4) F) (h1 : Gt * D = D * Gt) (h3 : Gs * D = D * Gs) :
    D = Matrix.diagonal (fun i => D i i) := by
  obtain ⟨b02, b03, b12, b13, b20, b30, b21, b31⟩ := blocks_vanish Gt D h2 rfl h1
  have e : ∀ i j : Fin 4, (Gs * D : Matrix (Fin 4) (Fin 4) F) i j = (D * Gs : Matrix (Fin 4) (Fin 4) F) i j :=
    fun i j => by rw [h3]
  have e01 := e 0 1
  have e10 := e 1 0
  have e23 := e 2 3
  have e32 := e 3 2
  simp [Gs, Matrix.mul_apply, Fin.sum_univ_four] at e01 e10 e23 e32
  have two : ∀ x : F, x + x = 0 → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have d01 : D 0 1 = 0 := two _ (by linear_combination e01)
  have d10 : D 1 0 = 0 := two _ (by linear_combination (-1 : F) * e10)
  have d23 : D 2 3 = 0 := two _ (by linear_combination e23)
  have d32 : D 3 2 = 0 := two _ (by linear_combination (-1 : F) * e32)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b02, b03, b12, b13, b20, b30, b21, b31, d01, d10, d23, d32]

theorem db_frame [Finite F] (hF4 : Nat.card F % 4 = 3) (B g h : Matrix (Fin 4) (Fin 4) F)
    (hdet : B.det ≠ 0) (hgg : g * g = 1) (hhh : h * h = 1) (hgh : g * h = h * g) (hgdet : g.det = 1)
    (hhdet : h.det = 1) (hg1 : g ≠ 1) (hgm1 : g ≠ -1) (hh1 : h ≠ 1) (hhm1 : h ≠ -1) (hhg : h ≠ g) (hhmg : h ≠ -g)
    (hgB : g * B = B * gᵀ) (hhB : h * B = B * hᵀ) :
    ∃ (P : GL (Fin 4) F) (d : Fin 4 → F), (∀ i, d i ≠ 0) ∧
      B = (P : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal d * (P : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      g * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Gt ∧
      h * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Gs := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨P, hgP, hhP⟩ := joint_frame hF4 g h hgg hhh hgh hgdet hhdet hg1 hgm1 hh1 hhm1 hhg hhmg
  have hGt : (Gt : Matrix (Fin 4) (Fin 4) F)ᵀ = Gt := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Gt]
  have hGs : (Gs : Matrix (Fin 4) (Fin 4) F)ᵀ = Gs := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Gs]
  have c1 := comm_of_frame hgP hGt hgB
  have c2 := comm_of_frame hhP hGs hhB
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  set D : Matrix (Fin 4) (Fin 4) F := Pi * B * Piᵀ with hDdef
  have hD := diag_of_comm h2 D c1 c2
  have hBeq : B = Pm * D * Pmᵀ := by
    have hPt' : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
    calc B = (Pm * Pi) * B * (Piᵀ * Pmᵀ) := by rw [hPP, hPt', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [hDdef]; simp only [Matrix.mul_assoc]
  refine ⟨P, fun i => D i i, ?_, ?_, hgP, hhP⟩
  · intro i hi
    have hdD : D.det ≠ 0 := by
      intro h0
      apply hdet
      rw [hBeq, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]
    rw [hD, Matrix.det_diagonal] at hdD
    exact hdD (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  · rw [← hD]
    exact hBeq

end DbFrame

section GenDb

variable {F : Type} [Field F]

theorem Gt_eq_diagonal : (Gt : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![1, 1, -1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gt]

theorem Gs_eq_diagonal : (Gs : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![1, -1, 1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gs]

theorem coe_planar_dgS (s : Fˣ) : (planar (dgS s) : Matrix (Fin 4) (Fin 4) F) =
    Matrix.diagonal ![(s : F), ((s⁻¹ : Fˣ) : F), 1, 1] := by
  rw [coe_planar]
  ext i j; fin_cases i <;> fin_cases j <;> simp [dgS]

theorem planar_dgS_comm_Gt (s : Fˣ) : (planar (dgS s) : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (planar (dgS s) : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_planar_dgS, Gt_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; ext i; fin_cases i <;> simp [mul_comm]

theorem planar_dgS_comm_Gs (s : Fˣ) : (planar (dgS s) : Matrix (Fin 4) (Fin 4) F) * Gs = Gs * (planar (dgS s) : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_planar_dgS, Gs_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; ext i; fin_cases i <;> simp [mul_comm]

theorem planar_comm_Gt (r : SL(2, F)) : (planar r : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (planar r : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_planar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gt, Matrix.mul_apply, Fin.sum_univ_four]

theorem planar_form (r : SL(2, F)) (c : Fin 4 → F)
    (h : (r : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal ![c 0, c 1] * (r : Matrix (Fin 2) (Fin 2) F)ᵀ =
      Matrix.diagonal ![c 0, c 1]) :
    (planar r : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal c * (planar r : Matrix (Fin 4) (Fin 4) F)ᵀ =
      Matrix.diagonal c := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] at e00 e01 e10 e11
  rw [coe_planar, diagonal_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | linear_combination e00 | linear_combination e01 | linear_combination e10 | linear_combination e11

theorem hypS_form (h2 : (2 : F) ≠ 0) (γ σ : Fˣ) (a c : F) (hc : c = -((γ : F) ^ 2) * a) :
    (hypS h2 γ σ : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal ![a, c] * (hypS h2 γ σ : Matrix (Fin 2) (Fin 2) F)ᵀ =
      Matrix.diagonal ![a, c] := by
  have hγ : (γ : F) ≠ 0 := γ.ne_zero
  have hσ : (σ : F) ≠ 0 := σ.ne_zero
  have hd : (Matrix.diagonal ![a, c] : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, c] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  subst hc
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypS, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

theorem rot02_comm_Gs (m y z : F) (h : m * m - y * z = 1) :
    (rot02 m y z h : Matrix (Fin 4) (Fin 4) F) * Gs = Gs * (rot02 m y z h : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_rot02]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gs, Matrix.mul_apply, Fin.sum_univ_four]

theorem rot13_comm_Gs (m y z : F) (h : m * m - y * z = 1) :
    (rot13 m y z h : Matrix (Fin 4) (Fin 4) F) * Gs = Gs * (rot13 m y z h : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_rot13]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gs, Matrix.mul_apply, Fin.sum_univ_four]

theorem gen_Db_core [Finite F] (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) (b : Fin 4 → F) (hb : ∀ i, b i ≠ 0)
    (Γ : Subgroup SL(4, F))
    (hT : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * Gs = Gs * (x : Matrix (Fin 4) (Fin 4) F) → x ∈ Γ)
    (hP1 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal b * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = Matrix.diagonal b → x ∈ Γ)
    (hP2 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * (Gs * Matrix.diagonal b) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
        Gs * Matrix.diagonal b → x ∈ Γ)
    (hP3 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * Gs = Gs * (x : Matrix (Fin 4) (Fin 4) F) →
      (x : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal b * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = Matrix.diagonal b → x ∈ Γ) :
    Γ = ⊤ := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Nat.card F % 2 = 1 := by omega
  obtain ⟨ρ, hρ4, hρ1, hρ5⟩ := exists_rho hF4 h7
  obtain ⟨ε, hε, γ, hγ⟩ := exists_sign hF4 (b 0) (b 1) (hb 0) (hb 1)
  have hD : ∀ s : Fˣ, planarHom (dgS s) ∈ Γ := fun s => hT _ (planar_dgS_comm_Gt s) (planar_dgS_comm_Gs s)
  have hG : ∀ σ : Fˣ, planarHom (hypS h2 γ σ) ∈ Γ := by
    intro σ
    rcases hε with rfl | rfl
    · have hc : b 1 = -((γ : F) ^ 2) * b 0 := by
        rw [hγ]
        have := hb 0
        field_simp
      exact hP1 _ (planar_comm_Gt _) (planar_form _ b (hypS_form h2 γ σ (b 0) (b 1) hc))
    · have hc : -(b 1) = -((γ : F) ^ 2) * b 0 := by
        rw [hγ]
        have := hb 0
        field_simp
      have e : Gs * Matrix.diagonal b = Matrix.diagonal ![b 0, -(b 1), b 2, -(b 3)] := by
        rw [Gs_eq_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        ext i; fin_cases i <;> simp
      refine hP2 _ (planar_comm_Gt _) ?_
      rw [e]
      exact planar_form _ ![b 0, -(b 1), b 2, -(b 3)] (by simpa using hypS_form h2 γ σ (b 0) (-(b 1)) hc)
  obtain ⟨h01, h10⟩ := plane_top hodd h2 γ ρ hρ4 hρ1 hρ5 Γ hD hG
  obtain ⟨m, y, z, hmyz, hy, hz, e1, e2, e3⟩ := rot_exists h7 h2 (b 0) (b 2) (hb 0) (hb 2)
  obtain ⟨m', y', z', hmyz', hy', hz', e1', e2', e3'⟩ := rot_exists h7 h2 (b 1) (b 3) (hb 1) (hb 3)
  have hr1 : rot02 m y z hmyz ∈ Γ := hP3 _ (rot02_comm_Gs m y z hmyz) (rot02_diag b m y z hmyz e1 e2 e3)
  have hr2 : rot13 m' y' z' hmyz' ∈ Γ := hP3 _ (rot13_comm_Gs m' y' z' hmyz') (rot13_diag b m' y' z' hmyz' e1' e2' e3')
  exact mix_top Γ h01 h10 m y z hmyz hy hz hr1 m' y' z' hmyz' hy' hz' hr2

end GenDb

section ClassDbThm

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem classDb (F : Type) [Field F] [Finite F] : ClassDb F := by
  intro hF4 h7 B g h hBt hdet hBd hgg hhh hgh hgdet hhdet hg1 hgm1 hh1 hhm1 hhg hhmg hgB hhB Γ hT hP1 hP2 hP3
  obtain ⟨P, d, hd, hBP, hgP, hhP⟩ := db_frame hF4 B g h hdet hgg hhh hgh hgdet hhdet hg1 hgm1 hh1 hhm1 hhg hhmg
    hgB hhB
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hPt : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPt' : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have eg : Pi * g * Pm = Gt := by
    rw [Matrix.mul_assoc, hgP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eh : Pi * h * Pm = Gs := by
    rw [Matrix.mul_assoc, hhP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eB : Pi * B * Piᵀ = Matrix.diagonal d := by
    rw [hBP]
    calc Pi * (Pm * Matrix.diagonal d * Pmᵀ) * Piᵀ = (Pi * Pm) * Matrix.diagonal d * (Pmᵀ * Piᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, hPt', Matrix.one_mul, Matrix.mul_one]
  have ehB : Pi * (h * B) * Piᵀ = Gs * Matrix.diagonal d := by
    rw [← eh, ← eB]
    calc Pi * (h * B) * Piᵀ = Pi * h * (Pm * Pi) * B * Piᵀ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine top_of_conj Γ P (gen_Db_core hF4 h7 d hd (Γ.comap (slConjugation 4 F P).toMonoidHom) ?_ ?_ ?_ ?_)
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hT _ ((conj_commute_iff P x g).2 (by rw [eg]; exact hx1)) ((conj_commute_iff P x h).2 (by rw [eh]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hP1 _ ((conj_commute_iff P x g).2 (by rw [eg]; exact hx1)) ((conj_form_iff P x B).2 (by rw [eB]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hP2 _ ((conj_commute_iff P x g).2 (by rw [eg]; exact hx1)) ((conj_form_iff P x (h * B)).2 (by rw [ehB]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hP3 _ ((conj_commute_iff P x h).2 (by rw [eh]; exact hx1)) ((conj_form_iff P x B).2 (by rw [eB]; exact hx2))

end ClassDbThm

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
