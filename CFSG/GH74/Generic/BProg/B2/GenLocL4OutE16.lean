module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutE16Gen

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups
section Mats

variable {F : Type} [Field F]

@[expose] def m1 : Matrix (Fin 4) (Fin 4) F := !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]
@[expose] def m2 : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
@[expose] def m3 : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]
@[expose] def m4 : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

@[expose] def mm : Fin 4 → Matrix (Fin 4) (Fin 4) F := ![m1, m2, m3, m4]

theorem m1_sq : (m1 : Matrix (Fin 4) (Fin 4) F) * m1 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m1, Matrix.mul_apply, Fin.sum_univ_four]
theorem m2_sq : (m2 : Matrix (Fin 4) (Fin 4) F) * m2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m2, Matrix.mul_apply, Fin.sum_univ_four]
theorem m3_sq : (m3 : Matrix (Fin 4) (Fin 4) F) * m3 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m3, Matrix.mul_apply, Fin.sum_univ_four]
theorem m4_sq : (m4 : Matrix (Fin 4) (Fin 4) F) * m4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m4, Matrix.mul_apply, Fin.sum_univ_four]

theorem m12 : (m1 : Matrix (Fin 4) (Fin 4) F) * m2 = -(m2 * m1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m1, m2, Matrix.mul_apply, Fin.sum_univ_four]
theorem m34 : (m3 : Matrix (Fin 4) (Fin 4) F) * m4 = -(m4 * m3) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m3, m4, Matrix.mul_apply, Fin.sum_univ_four]
theorem m13 : (m1 : Matrix (Fin 4) (Fin 4) F) * m3 = m3 * m1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m1, m3, Matrix.mul_apply, Fin.sum_univ_four]
theorem m14 : (m1 : Matrix (Fin 4) (Fin 4) F) * m4 = m4 * m1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m1, m4, Matrix.mul_apply, Fin.sum_univ_four]
theorem m23 : (m2 : Matrix (Fin 4) (Fin 4) F) * m3 = m3 * m2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m2, m3, Matrix.mul_apply, Fin.sum_univ_four]
theorem m24 : (m2 : Matrix (Fin 4) (Fin 4) F) * m4 = m4 * m2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m2, m4, Matrix.mul_apply, Fin.sum_univ_four]

theorem m1_t : (m1 : Matrix (Fin 4) (Fin 4) F)ᵀ = -m1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m1]
theorem m2_t : (m2 : Matrix (Fin 4) (Fin 4) F)ᵀ = m2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m2]
theorem m3_t : (m3 : Matrix (Fin 4) (Fin 4) F)ᵀ = -m3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m3]
theorem m4_t : (m4 : Matrix (Fin 4) (Fin 4) F)ᵀ = m4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [m4]

theorem det_m1 : (m1 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [m1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_m2 : (m2 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [m2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_m3 : (m3 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [m3, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
theorem det_m4 : (m4 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [m4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

end Mats


section Lift

variable {F : Type} [Field F]

theorem det_conj_eq (P : GL (Fin 4) F) (m : Matrix (Fin 4) (Fin 4) F) :
    ((P : Matrix (Fin 4) (Fin 4) F) * m * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det = m.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.det_one, one_mul]

@[expose] def lift (P : GL (Fin 4) F) (m : Matrix (Fin 4) (Fin 4) F) (hm : m.det = 1) : Matrix.SpecialLinearGroup (Fin 4) F :=
  ⟨(P : Matrix (Fin 4) (Fin 4) F) * m * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), by rw [det_conj_eq, hm]⟩

theorem coe_lift (P : GL (Fin 4) F) (m : Matrix (Fin 4) (Fin 4) F) (hm : m.det = 1) :
    ((lift P m hm : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * m * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := rfl

theorem PPi' (P : GL (Fin 4) F) :
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem PPi (P : GL (Fin 4) F) :
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem PiP' (P : GL (Fin 4) F) :
    (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem PiP (P : GL (Fin 4) F) :
    (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conj_mul' (P : GL (Fin 4) F) (m n : Matrix (Fin 4) (Fin 4) F) :
    (P : Matrix (Fin 4) (Fin 4) F) * m * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((P : Matrix (Fin 4) (Fin 4) F) * n * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
    (P : Matrix (Fin 4) (Fin 4) F) * (m * n) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  calc _ = (P : Matrix (Fin 4) (Fin 4) F) * m * (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)) * n *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [PPi, Matrix.mul_one]; simp only [Matrix.mul_assoc]

@[expose] def zN : Matrix.SpecialLinearGroup (Fin 4) F :=
  ⟨-1, by rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num⟩

theorem coe_zN : ((zN : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := rfl

theorem zN_mem_center : (zN : Matrix.SpecialLinearGroup (Fin 4) F) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_zN]

theorem zN_mul_self : (zN : Matrix.SpecialLinearGroup (Fin 4) F) * zN = 1 := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_zN]

theorem zN_ne_one (h2 : (2 : F) ≠ 0) : (zN : Matrix.SpecialLinearGroup (Fin 4) F) ≠ 1 := by
  intro h
  have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simp [coe_zN] at this
  apply h2
  linear_combination -this

end Lift

section Main

variable {F : Type} [Field F]

theorem det_mm (i : Fin 4) : (mm i : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  fin_cases i
  · exact det_m1
  · exact det_m2
  · exact det_m3
  · exact det_m4

@[expose] def gl (P : GL (Fin 4) F) : Fin 4 → Matrix.SpecialLinearGroup (Fin 4) F := fun i => lift P (mm i) (det_mm i)

theorem lift_mul_comm {P : GL (Fin 4) F} {m n : Matrix (Fin 4) (Fin 4) F} (hm : m.det = 1) (hn : n.det = 1)
    (h : m * n = n * m) : lift P m hm * lift P n hn = lift P n hn * lift P m hm := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lift, conj_mul', h]

theorem lift_mul_anticomm {P : GL (Fin 4) F} {m n : Matrix (Fin 4) (Fin 4) F} (hm : m.det = 1) (hn : n.det = 1)
    (h : m * n = -(n * m)) : lift P m hm * lift P n hn = zN * (lift P n hn * lift P m hm) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lift, coe_zN]
  rw [conj_mul', conj_mul', h]
  simp

theorem lift_sq {P : GL (Fin 4) F} {m : Matrix (Fin 4) (Fin 4) F} (hm : m.det = 1) (h : m * m = 1 ∨ m * m = -1) :
    lift P m hm * lift P m hm = 1 ∨ lift P m hm * lift P m hm = zN := by
  rcases h with h | h
  · left
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lift, conj_mul', h, Matrix.mul_one, PiP]
    simp
  · right
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lift, conj_mul', h, coe_zN, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_one, PiP]

end Main

section MainB

variable {F : Type} [Field F]

theorem mm_mul_t (i : Fin 4) : (mm i : Matrix (Fin 4) (Fin 4) F) * (mm i : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
  fin_cases i
  · show m1 * m1ᵀ = 1
    rw [m1_t, Matrix.mul_neg, m1_sq, neg_neg]
  · show m2 * m2ᵀ = 1
    rw [m2_t, m2_sq]
  · show m3 * m3ᵀ = 1
    rw [m3_t, Matrix.mul_neg, m3_sq, neg_neg]
  · show m4 * m4ᵀ = 1
    rw [m4_t, m4_sq]

theorem gl_inv (P : GL (Fin 4) F) (i : Fin 4) :
    ((gl P i)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) =
      lift P ((mm i : Matrix (Fin 4) (Fin 4) F)ᵀ) (by rw [Matrix.det_transpose]; exact det_mm i) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  simp only [gl, Matrix.SpecialLinearGroup.coe_mul, coe_lift, conj_mul', mm_mul_t, Matrix.mul_one, PiP]
  rfl

theorem u_gl {B P : GL (Fin 4) F} {N : Matrix (Fin 4) (Fin 4) F}
    (hBN : (B : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * N * (P : Matrix (Fin 4) (Fin 4) F)ᵀ)
    (u : MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hu : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F, ((u g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (i : Fin 4)
    (hN : N * mm i = mm i * N ∨ N * mm i = -(mm i * N)) :
    u (gl P i) = gl P i ∨ u (gl P i) = zN * gl P i := by
  have hBB : (B : Matrix (Fin 4) (Fin 4) F) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := PiP' B
  have hX : ((((gl P i)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).transpose =
      ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose * (mm i) * (P : Matrix (Fin 4) (Fin 4) F).transpose := by
    rw [gl_inv, coe_lift, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  have hPt : (P : Matrix (Fin 4) (Fin 4) F).transpose * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose = 1 := by
    rw [← Matrix.transpose_mul, PPi, Matrix.transpose_one]
  have hBX : (B : Matrix (Fin 4) (Fin 4) F) * ((((gl P i)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).transpose =
      (P : Matrix (Fin 4) (Fin 4) F) * (N * mm i) * (P : Matrix (Fin 4) (Fin 4) F).transpose := by
    rw [hX, hBN]
    calc _ = (P : Matrix (Fin 4) (Fin 4) F) * N * ((P : Matrix (Fin 4) (Fin 4) F).transpose * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose) * (mm i) * (P : Matrix (Fin 4) (Fin 4) F).transpose := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hgB : ((gl P i : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * (mm i * N) * (P : Matrix (Fin 4) (Fin 4) F).transpose := by
    rw [hBN, gl, coe_lift]
    calc _ = (P : Matrix (Fin 4) (Fin 4) F) * (mm i) * (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)) * N * (P : Matrix (Fin 4) (Fin 4) F).transpose := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [PPi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hBiB : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) = 1 := PPi' B
  have key : ((u (gl P i) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * ((((gl P i)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).transpose := by
    rw [hu, Matrix.mul_assoc, hBiB, Matrix.mul_one]
  have cancel : ∀ X Y : Matrix (Fin 4) (Fin 4) F, X * (B : Matrix (Fin 4) (Fin 4) F) = Y * (B : Matrix (Fin 4) (Fin 4) F) → X = Y := by
    intro X Y h
    calc X = X * ((B : Matrix (Fin 4) (Fin 4) F) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by rw [hBB, Matrix.mul_one]
      _ = (X * (B : Matrix (Fin 4) (Fin 4) F)) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [Matrix.mul_assoc]
      _ = (Y * (B : Matrix (Fin 4) (Fin 4) F)) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [h]
      _ = Y := by rw [Matrix.mul_assoc, hBB, Matrix.mul_one]
  rcases hN with h | h
  · left
    apply Subtype.ext
    apply cancel
    rw [key, hBX, hgB, h]
  · right
    apply Subtype.ext
    apply cancel
    rw [key, hBX, Matrix.SpecialLinearGroup.coe_mul, coe_zN, Matrix.mul_assoc (-1 : Matrix (Fin 4) (Fin 4) F) _ _, hgB, h]
    simp

end MainB

section Final

variable {F : Type} [Field F] [Finite F]

theorem not_sectional_of_graph_form (h2 : (2 : F) ≠ 0) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (a : A)
    (hnin : α a ∉ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 4) F →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)).range)
    (B P : GL (Fin 4) F) (N : Matrix (Fin 4) (Fin 4) F)
    (hBN : (B : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * N * (P : Matrix (Fin 4) (Fin 4) F)ᵀ)
    (hu : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F, ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (B : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hN : ∀ i, N * mm i = mm i * N ∨ N * mm i = -(mm i * N)) :
    ¬ SectionalTwoRankLE ↥(innJoin α) 4 := by
  have hsq : ∀ i, gl P i * gl P i = 1 ∨ gl P i * gl P i = zN := by
    intro i
    fin_cases i
    · exact lift_sq (det_mm 0) (Or.inr m1_sq)
    · exact lift_sq (det_mm 1) (Or.inl m2_sq)
    · exact lift_sq (det_mm 2) (Or.inr m3_sq)
    · exact lift_sq (det_mm 3) (Or.inl m4_sq)
  obtain ⟨V, hVinn, hVea, hVcard, hVcomm⟩ := exists_E16 zN_mem_center zN_mul_self (zN_ne_one h2) (gl P) hsq
    (lift_mul_anticomm (det_mm 0) (det_mm 1) m12) (lift_mul_anticomm (det_mm 2) (det_mm 3) m34)
    (lift_mul_comm (det_mm 0) (det_mm 2) m13) (lift_mul_comm (det_mm 0) (det_mm 3) m14)
    (lift_mul_comm (det_mm 1) (det_mm 2) m23) (lift_mul_comm (det_mm 1) (det_mm 3) m24)
  exact not_sectional_of_E16 hA α a hnin V hVinn hVea hVcard
    (hVcomm (α a) (fun i => u_gl hBN (α a) hu i (hN i)))

end Final


end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
