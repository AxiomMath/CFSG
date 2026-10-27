module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutMix
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutNF

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG Matrix
open scoped MatrixGroups


section Rot

variable {F : Type} [Field F]

theorem exists_tau [Finite F] (hF : 7 ≤ Nat.card F) (κ : F) (hκ : κ ≠ 0) :
    ∃ τ : F, τ ≠ 0 ∧ 1 + κ * τ ^ 2 ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra h
  push Not at h
  have hcard : Finset.card ({0, 1, -1} : Finset F) < Finset.card (Finset.univ : Finset F) := by
    have h1 : Finset.card ({0, 1, -1} : Finset F) ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hτ
  obtain ⟨h0, h1, h2⟩ := hτ
  have e1 := h τ h0
  have e2 := h 1 one_ne_zero
  have : τ ^ 2 = 1 := by
    have : κ * τ ^ 2 = κ * 1 ^ 2 := by linear_combination e1 - e2
    simpa [hκ] using this
  have h3 : (τ - 1) * (τ + 1) = 0 := by linear_combination this
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact h1 (sub_eq_zero.1 h4)
  · exact h2 (eq_neg_of_add_eq_zero_left h4)

theorem rot_exists [Finite F] (hF : 7 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) (d0 d2 : F) (h0 : d0 ≠ 0) (h2' : d2 ≠ 0) :
    ∃ (m y z : F), m * m - y * z = 1 ∧ y ≠ 0 ∧ z ≠ 0 ∧ m * m * d0 + y * y * d2 = d0 ∧
      m * z * d0 + y * m * d2 = 0 ∧ z * z * d0 + m * m * d2 = d2 := by
  obtain ⟨κ, hκ⟩ : ∃ κ, d2 = κ * d0 := ⟨d2 / d0, by field_simp⟩
  subst hκ
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul h2'
  obtain ⟨τ, hτ0, hτ1⟩ := exists_tau hF κ hκ0
  refine ⟨(1 - κ * τ ^ 2) / (1 + κ * τ ^ 2), 2 * τ / (1 + κ * τ ^ 2), -κ * (2 * τ / (1 + κ * τ ^ 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · exact div_ne_zero (mul_ne_zero h2 hτ0) hτ1
  · exact mul_ne_zero (neg_ne_zero.2 hκ0) (div_ne_zero (mul_ne_zero h2 hτ0) hτ1)
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring

end Rot

section Frame

variable {F : Type} [Field F]

theorem diagonal_four (d : Fin 4 → F) :
    (Matrix.diagonal d : Matrix (Fin 4) (Fin 4) F) =
      !![d 0, 0, 0, 0; 0, d 1, 0, 0; 0, 0, d 2, 0; 0, 0, 0, d 3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem rot02_diag (d : Fin 4 → F) (m y z : F) (h : m * m - y * z = 1) (h1 : m * m * d 0 + y * y * d 2 = d 0)
    (h2 : m * z * d 0 + y * m * d 2 = 0) (h3 : z * z * d 0 + m * m * d 2 = d 2) :
    (rot02 m y z h : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal d * (rot02 m y z h : Matrix (Fin 4) (Fin 4) F)ᵀ =
      Matrix.diagonal d := by
  rw [coe_rot02, diagonal_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | linear_combination h1 | linear_combination h3 | linear_combination h2

theorem rot13_diag (d : Fin 4 → F) (m y z : F) (h : m * m - y * z = 1) (h1 : m * m * d 1 + y * y * d 3 = d 1)
    (h2 : m * z * d 1 + y * m * d 3 = 0) (h3 : z * z * d 1 + m * m * d 3 = d 3) :
    (rot13 m y z h : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal d * (rot13 m y z h : Matrix (Fin 4) (Fin 4) F)ᵀ =
      Matrix.diagonal d := by
  rw [coe_rot13, diagonal_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | linear_combination h1 | linear_combination h3 | linear_combination h2

end Frame

section SplitFrame

variable {F : Type} [Field F]

open CFSG.ComponentClassification.CatFactsL4U4.HBlocks in
theorem X1_one : (X1 (1 : F)) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := rfl

theorem blocks_vanish (D Bp : Matrix (Fin 4) (Fin 4) F) (h2 : (2 : F) ≠ 0)
    (hD : D = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) (hcomm : D * Bp = Bp * D) :
    Bp 0 2 = 0 ∧ Bp 0 3 = 0 ∧ Bp 1 2 = 0 ∧ Bp 1 3 = 0 ∧ Bp 2 0 = 0 ∧ Bp 3 0 = 0 ∧ Bp 2 1 = 0 ∧ Bp 3 1 = 0 := by
  have e : ∀ i j, (D * Bp) i j = (Bp * D) i j := fun i j => by rw [hcomm]
  subst hD
  have h02 := e 0 2
  have h03 := e 0 3
  have h12 := e 1 2
  have h13 := e 1 3
  have h20 := e 2 0
  have h30 := e 3 0
  have h21 := e 2 1
  have h31 := e 3 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h02 h03 h12 h13 h20 h30 h21 h31
  have two : ∀ x : F, x + x = 0 → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.1 this).resolve_left h2
  refine ⟨two _ (by linear_combination h02), two _ (by linear_combination h03), two _ (by linear_combination h12),
    two _ (by linear_combination h13), two _ (by linear_combination (-1 : F) * h20), two _ (by linear_combination (-1 : F) * h30),
    two _ (by linear_combination (-1 : F) * h21), two _ (by linear_combination (-1 : F) * h31)⟩

end SplitFrame

section SplitFrame2

variable {F : Type} [Field F]

theorem split_frame [Finite F] (hF4 : Nat.card F % 4 = 3) (B g : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = B)
    (hdet : B.det ≠ 0) (hgg : g * g = 1) (hg1 : g ≠ 1) (hgm1 : g ≠ -1) (hgdet : g.det = 1) (hgB : g * B = B * gᵀ) :
    ∃ (P : GL (Fin 4) F) (d : Fin 4 → F), (∀ i, d i ≠ 0) ∧
      B = (P : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal d * (P : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      g * (P : Matrix (Fin 4) (Fin 4) F) =
        (P : Matrix (Fin 4) (Fin 4) F) * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨P0, hP0⟩ := CFSG.ComponentClassification.CatFactsL4U4.TBlocks.exists_frame_t2_L4 h2 hgg hgdet hg1 hgm1
  rw [X1_one] at hP0
  set D : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] with hD
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P0⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPP : (P0 : Matrix (Fin 4) (Fin 4) F) * Pi = 1 := by rw [hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * (P0 : Matrix (Fin 4) (Fin 4) F) = 1 := by rw [hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDt : Dᵀ = D := by ext i j; fin_cases i <;> fin_cases j <;> simp [hD]
  have hg_eq : g = (P0 : Matrix (Fin 4) (Fin 4) F) * D * Pi := by
    calc g = g * ((P0 : Matrix (Fin 4) (Fin 4) F) * Pi) := by rw [hPP, Matrix.mul_one]
      _ = (g * (P0 : Matrix (Fin 4) (Fin 4) F)) * Pi := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hP0]
  set Bp : Matrix (Fin 4) (Fin 4) F := Pi * B * Piᵀ with hBp
  have hBpt : Bpᵀ = Bp := by
    rw [hBp, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBt, Matrix.mul_assoc]
  have hcomm : D * Bp = Bp * D := by
    have h1 : D * Bp = Pi * g * B * Piᵀ := by
      rw [hg_eq, hBp]
      calc D * (Pi * B * Piᵀ) = (Pi * (P0 : Matrix (Fin 4) (Fin 4) F)) * D * Pi * B * Piᵀ := by
            rw [hPiP, Matrix.one_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have h2' : Bp * D = Pi * (B * gᵀ) * Piᵀ := by
      rw [hg_eq, hBp, Matrix.transpose_mul, Matrix.transpose_mul, hDt]
      calc Pi * B * Piᵀ * D = Pi * B * (Piᵀ * D * ((P0 : Matrix (Fin 4) (Fin 4) F)ᵀ * Piᵀ)) := by
            rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [h1, h2', ← hgB]
    simp only [Matrix.mul_assoc]
  obtain ⟨b02, b03, b12, b13, b20, b30, b21, b31⟩ := blocks_vanish D Bp h2 hD hcomm
  have hs01 : Bp 0 1 = Bp 1 0 := by have := congrFun (congrFun hBpt 0) 1; simpa using this.symm
  have hs23 : Bp 2 3 = Bp 3 2 := by have := congrFun (congrFun hBpt 2) 3; simpa using this.symm
  set B1 : Matrix (Fin 2) (Fin 2) F := !![Bp 0 0, Bp 0 1; Bp 1 0, Bp 1 1] with hB1
  set B2 : Matrix (Fin 2) (Fin 2) F := !![Bp 2 2, Bp 2 3; Bp 3 2, Bp 3 3] with hB2
  have hB1t : B1ᵀ = B1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [hB1, hs01]
  have hB2t : B2ᵀ = B2 := by ext i j; fin_cases i <;> fin_cases j <;> simp [hB2, hs23]
  obtain ⟨Q1, hQ1⟩ := GenLocL5Sign.exists_orthogonal_congr hK B1 hB1t
  obtain ⟨Q2, hQ2⟩ := GenLocL5Sign.exists_orthogonal_congr hK B2 hB2t
  have e1 := hQ1 0 1 (by decide)
  have e1' := hQ1 1 0 (by decide)
  have e2 := hQ2 0 1 (by decide)
  have e2' := hQ2 1 0 (by decide)
  simp only [hB1, hB2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons,
    Matrix.head_fin_const] at e1 e1' e2 e2'
  set Qm : Matrix (Fin 4) (Fin 4) F :=
    !![(Q1 : Matrix (Fin 2) (Fin 2) F) 0 0, (Q1 : Matrix (Fin 2) (Fin 2) F) 0 1, 0, 0;
       (Q1 : Matrix (Fin 2) (Fin 2) F) 1 0, (Q1 : Matrix (Fin 2) (Fin 2) F) 1 1, 0, 0;
       0, 0, (Q2 : Matrix (Fin 2) (Fin 2) F) 0 0, (Q2 : Matrix (Fin 2) (Fin 2) F) 0 1;
       0, 0, (Q2 : Matrix (Fin 2) (Fin 2) F) 1 0, (Q2 : Matrix (Fin 2) (Fin 2) F) 1 1] with hQm
  have hdQ1 : (Q1 : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q1.isUnit).ne_zero
  have hdQ2 : (Q2 : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q2.isUnit).ne_zero
  have hdQm : Qm.det = (Q1 : Matrix (Fin 2) (Fin 2) F).det * (Q2 : Matrix (Fin 2) (Fin 2) F).det := by
    simp only [hQm, Matrix.det_fin_two]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  have hdQ : Qm.det ≠ 0 := by rw [hdQm]; exact mul_ne_zero hdQ1 hdQ2
  have hDQ : D * Qm = Qm * D := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, hQm, Matrix.mul_apply, Fin.sum_univ_four]
  set Δ : Matrix (Fin 4) (Fin 4) F := Qmᵀ * Bp * Qm with hΔdef
  have hΔ : ∀ i j, i ≠ j → Δ i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (simp [hΔdef, Matrix.mul_apply, Fin.sum_univ_four, hQm, b02, b03, b12, b13, b20, b30, b21, b31]; done)
      | (simp [hΔdef, Matrix.mul_apply, Fin.sum_univ_four, hQm, b02, b03, b12, b13, b20, b30, b21, b31]
         first | linear_combination e1 | linear_combination e1' | linear_combination e2 | linear_combination e2')
  have hΔdiag : Δ = Matrix.diagonal (fun i => Δ i i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h]; exact hΔ i j h
  have hdPi : Pi.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPiP
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetΔ : Δ.det ≠ 0 := by
    rw [hΔdef, hBp, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hdQ (mul_ne_zero (mul_ne_zero hdPi hdet) hdPi)) hdQ
  have hd : ∀ i, Δ i i ≠ 0 := by
    intro i h0
    apply hdetΔ
    rw [hΔdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  set Qg : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Qm hdQ with hQg
  have hQgc : (Qg : Matrix (Fin 4) (Fin 4) F) = Qm := rfl
  set Qi : Matrix (Fin 4) (Fin 4) F := ((Qg⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hQi
  have hQQi : Qm * Qi = 1 := by rw [hQi, ← hQgc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * Qm = 1 := by rw [hQi, ← hQgc, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdQi : Qi.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hQiQ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdP : ((P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 P0.isUnit).ne_zero hdQi
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero ((P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ) hdP : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = (P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero ((P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ) hdP, fun i => Δ i i, hd, ?_, ?_⟩
  · rw [hcoe, ← hΔdiag]
    have hBpQ : Qiᵀ * Δ * Qi = Bp := by
      rw [hΔdef]
      calc Qiᵀ * (Qmᵀ * Bp * Qm) * Qi = (Qiᵀ * Qmᵀ) * Bp * (Qm * Qi) := by simp only [Matrix.mul_assoc]
        _ = Bp := by rw [← Matrix.transpose_mul, hQQi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    have hmain : (P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ * Δ * ((P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ)ᵀ = B := by
      calc (P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ * Δ * ((P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ)ᵀ
          = (P0 : Matrix (Fin 4) (Fin 4) F) * (Qiᵀ * Δ * Qi) * (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ := by
            rw [Matrix.transpose_mul, Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]
        _ = (P0 : Matrix (Fin 4) (Fin 4) F) * Bp * (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [hBpQ]
        _ = ((P0 : Matrix (Fin 4) (Fin 4) F) * Pi) * B * ((P0 : Matrix (Fin 4) (Fin 4) F) * Pi)ᵀ := by
            rw [hBp, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = B := by rw [hPP, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    exact hmain.symm
  · rw [hcoe]
    have hDQit : D * Qiᵀ = Qiᵀ * D := by
      have h1 : Qmᵀ * D = D * Qmᵀ := by
        have := congrArg Matrix.transpose hDQ
        rwa [Matrix.transpose_mul, Matrix.transpose_mul, hDt] at this
      calc D * Qiᵀ = (Qiᵀ * Qmᵀ) * D * Qiᵀ := by
            rw [← Matrix.transpose_mul, hQQi, Matrix.transpose_one, Matrix.one_mul]
        _ = Qiᵀ * (Qmᵀ * D) * Qiᵀ := by simp only [Matrix.mul_assoc]
        _ = Qiᵀ * (D * Qmᵀ) * Qiᵀ := by rw [h1]
        _ = Qiᵀ * D * (Qmᵀ * Qiᵀ) := by simp only [Matrix.mul_assoc]
        _ = Qiᵀ * D := by rw [← Matrix.transpose_mul, hQiQ, Matrix.transpose_one, Matrix.mul_one]
    calc g * ((P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ) = (g * (P0 : Matrix (Fin 4) (Fin 4) F)) * Qiᵀ := by
          rw [Matrix.mul_assoc]
      _ = (P0 : Matrix (Fin 4) (Fin 4) F) * (D * Qiᵀ) := by rw [hP0, Matrix.mul_assoc]
      _ = (P0 : Matrix (Fin 4) (Fin 4) F) * Qiᵀ * D := by rw [hDQit, Matrix.mul_assoc]

end SplitFrame2

section GenSplit

variable {F : Type} [Field F]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem top_of_conj (Γ : Subgroup SL(4, F)) (P : GL (Fin 4) F)
    (h : Γ.comap (slConjugation 4 F P).toMonoidHom = ⊤) : Γ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hy : (slConjugation 4 F P).symm x ∈ Γ.comap (slConjugation 4 F P).toMonoidHom := by
    rw [h]; exact Subgroup.mem_top _
  rw [Subgroup.mem_comap] at hy
  simpa using hy

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem coe_conj (P : GL (Fin 4) F) (z : SL(4, F)) :
    (((slConjugation 4 F P).toMonoidHom z : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * (z : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation P z

end GenSplit

section GenSplit2

variable {F : Type} [Field F]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem gen_split [Finite F] (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) (B g : Matrix (Fin 4) (Fin 4) F)
    (hBt : Bᵀ = B) (hdet : B.det ≠ 0) (hgg : g * g = 1) (hg1 : g ≠ 1) (hgm1 : g ≠ -1) (hgdet : g.det = 1)
    (hgB : g * B = B * gᵀ) (Γ : Subgroup SL(4, F))
    (h1 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * g = g * (x : Matrix (Fin 4) (Fin 4) F) → x ∈ Γ)
    (h2 : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * B * (x : Matrix (Fin 4) (Fin 4) F)ᵀ = B → x ∈ Γ) :
    Γ = ⊤ := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨P, d, hd, hBP, hgP⟩ := split_frame hF4 B g hBt hdet hgg hg1 hgm1 hgdet hgB
  set D : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] with hD
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F) with hPm
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPP : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg_eq : g = Pm * D * Pi := by
    calc g = g * (Pm * Pi) := by rw [hPP, Matrix.mul_one]
      _ = (g * Pm) * Pi := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hgP]
  set Γ' : Subgroup SL(4, F) := Γ.comap (slConjugation 4 F P).toMonoidHom with hΓ'
  have hmem : ∀ z : SL(4, F), z ∈ Γ' ↔ (slConjugation 4 F P).toMonoidHom z ∈ Γ := fun z => Iff.rfl
  have hplanar : ∀ (i j : Fin 4) (hij : i ≠ j) (a : F), (D * (1 + Matrix.single i j a) = (1 + Matrix.single i j a) * D) →
      tv i j hij a ∈ Γ' := by
    intro i j hij a hcomm
    rw [hmem]
    apply h1
    rw [coe_conj, coe_tv, hg_eq, ← hPi]
    rw [conj_mul', conj_mul', ← hcomm]
  have h01 : ∀ a, tv 0 1 (by decide) a ∈ Γ' := fun a => hplanar 0 1 (by decide) a (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply])
  have h10 : ∀ a, tv 1 0 (by decide) a ∈ Γ' := fun a => hplanar 1 0 (by decide) a (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply])
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  obtain ⟨m, y, z, hmyz, hy, hz, e1, e2, e3⟩ := rot_exists h7 h2' (d 0) (d 2) hd0 hd2
  obtain ⟨m', y', z', hmyz', hy', hz', e1', e2', e3'⟩ := rot_exists h7 h2' (d 1) (d 3) hd1 hd3
  have hpres : ∀ r : SL(4, F), (r : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal d * (r : Matrix (Fin 4) (Fin 4) F)ᵀ =
      Matrix.diagonal d → r ∈ Γ' := by
    intro r hr
    rw [hmem]
    apply h2
    rw [coe_conj, hBP, ← hPi]
    have hPt : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
    calc Pm * (r : Matrix (Fin 4) (Fin 4) F) * Pi * (Pm * Matrix.diagonal d * Pmᵀ) * (Pm * (r : Matrix (Fin 4) (Fin 4) F) * Pi)ᵀ
        = Pm * (r : Matrix (Fin 4) (Fin 4) F) * (Pi * Pm) * Matrix.diagonal d * (Pmᵀ * Piᵀ) * (r : Matrix (Fin 4) (Fin 4) F)ᵀ * Pmᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Pm * ((r : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal d * (r : Matrix (Fin 4) (Fin 4) F)ᵀ) * Pmᵀ := by
          rw [hPiP, hPt]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Pm * Matrix.diagonal d * Pmᵀ := by rw [hr]
  have hr1 : rot02 m y z hmyz ∈ Γ' := hpres _ (rot02_diag d m y z hmyz e1 e2 e3)
  have hr2 : rot13 m' y' z' hmyz' ∈ Γ' := hpres _ (rot13_diag d m' y' z' hmyz' e1' e2' e3')
  exact top_of_conj Γ P (mix_top Γ' h01 h10 m y z hmyz hy hz hr1 m' y' z' hmyz' hy' hz' hr2)

end GenSplit2


end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
