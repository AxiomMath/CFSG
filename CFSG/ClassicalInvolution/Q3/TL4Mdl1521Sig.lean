module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.E1521

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem card3_three_eq_zero [Finite F] (hF : Nat.card F = 3) : (3 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h
  exact_mod_cast h

theorem card3_two_ne_zero [Finite F] (hF : Nat.card F = 3) : (2 : F) ≠ 0 := fun h =>
  one_ne_zero (α := F) (by linear_combination card3_three_eq_zero hF - h)

theorem card3_mul_self (hF : Nat.card F = 3) {a : F} (ha : a ≠ 0) : a * a = 1 := by
  rw [← sq]
  exact Q3T6.sq_eq_one_of_card_three hF ha

theorem card3_ringEquiv [Finite F] (hF : Nat.card F = 3) (σ : F ≃+* F) : σ = RingEquiv.refl F := by
  refine RingEquiv.ext fun x => ?_
  have h3 : x * (x - 1) * (x + 1) = 0 := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hF] at h
    linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · rw [h5, map_zero]; rfl
    · rw [sub_eq_zero.mp h5, map_one]; rfl
  · rw [eq_neg_of_add_eq_zero_left h4, map_neg, map_one]; rfl

abbrev blk (a p q r s : F) : Matrix (Fin 4) (Fin 4) F :=
  !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, p, q; 0, 0, r, s]

theorem blk_mul (a p q r s a' p' q' r' s' : F) :
    blk a p q r s * blk a' p' q' r' s' =
      blk (a * a') (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem blk_inj {a p q r s a' p' q' r' s' : F} (h : blk a p q r s = blk a' p' q' r' s') :
    a = a' ∧ p = p' ∧ q = q' ∧ r = r' ∧ s = s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrFun (congrFun h 0) 0
  · simpa using congrFun (congrFun h 2) 2
  · simpa using congrFun (congrFun h 2) 3
  · simpa using congrFun (congrFun h 3) 2
  · simpa using congrFun (congrFun h 3) 3

theorem blk_congr {a p q r s a' p' q' r' s' : F} (ha : a = a') (hp : p = p') (hq : q = q')
    (hr : r = r') (hs : s = s') : blk a p q r s = blk a' p' q' r' s' := by
  rw [ha, hp, hq, hr, hs]

theorem smul_blk (c a p q r s : F) :
    c • blk a p q r s = blk (c * a) (c * p) (c * q) (c * r) (c * s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem smul_one_eq_blk (c : F) : c • (1 : Matrix (Fin 4) (Fin 4) F) = blk c c 0 0 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem det_blk (a p q r s : F) : (blk a p q r s).det = a * a * (p * s - q * r) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

abbrev blkJ (b p q r s : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, b, 0, 0; -b, 0, 0, 0; 0, 0, p, q; 0, 0, r, s]

theorem det_blkJ (b p q r s : F) : (blkJ b p q r s).det = b * b * (p * s - q * r) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

@[expose] def qI (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def qJ (h3 : (3 : F) = 0) : SL(2, F) :=
  ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; linear_combination -h3⟩

@[expose] noncomputable def blockQ0 (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  (commutator SL(2, F)).map ((proj 4 F).comp (blockSL F 4 2 0 (by norm_num)))

theorem mem_blockQ0 {c : SL(2, F)} (hc : c ∈ commutator SL(2, F)) :
    proj 4 F (blockSL F 4 2 0 (by norm_num) c) ∈ blockQ0 F :=
  Subgroup.mem_map_of_mem _ hc

theorem qI_pow : qI F ^ 2 ^ 2 = 1 := by
  apply Subtype.ext
  have h : ((qI F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (qI F : SL(2, F)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qI, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.SpecialLinearGroup.coe_pow, show 2 ^ 2 = 2 + 2 from rfl, pow_add, sq, h]
  simp

theorem qJ_pow (h3 : (3 : F) = 0) : qJ h3 ^ 2 ^ 2 = 1 := by
  apply Subtype.ext
  have h : ((qJ h3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (qJ h3 : SL(2, F)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h3
  rw [Matrix.SpecialLinearGroup.coe_pow, show 2 ^ 2 = 2 + 2 from rfl, pow_add, sq, h]
  simp

theorem odd_card_ker_id : Odd (Nat.card (MonoidHom.id SL(2, F)).ker) := by
  rw [(MonoidHom.ker_eq_bot_iff _).mpr Function.injective_id, Subgroup.card_bot]
  exact odd_one

theorem qI_mem (hF : Nat.card F = 3) : qI F ∈ commutator SL(2, F) :=
  Q3T6.mem_commutator_of_two_element_of_oddKernel_of_card_three hF (MonoidHom.id _)
    Function.surjective_id odd_card_ker_id ⟨2, qI_pow⟩

theorem qJ_mem (hF : Nat.card F = 3) (h3 : (3 : F) = 0) : qJ h3 ∈ commutator SL(2, F) :=
  Q3T6.mem_commutator_of_two_element_of_oddKernel_of_card_three hF (MonoidHom.id _)
    Function.surjective_id odd_card_ker_id ⟨2, qJ_pow h3⟩

abbrev mI (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev mJ (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev mJ' (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, -1, 0, 0; -1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem coe_block_qI :
    ((blockSL F 4 2 0 (by norm_num) (qI F) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = mI F := by
  rw [WeakCT.coe_blockSL, blockMat_four_zero]
  simp [qI]

theorem coe_block_qJ (h3 : (3 : F) = 0) :
    ((blockSL F 4 2 0 (by norm_num) (qJ h3) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = mJ F := by
  rw [WeakCT.coe_blockSL, blockMat_four_zero]
  simp [qJ]

theorem coe_block_inv_transpose (X : SL(2, F)) :
    ((((blockSL F 4 2 0 (by norm_num) X)⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![(X : Matrix (Fin 2) (Fin 2) F) 1 1, -(X : Matrix (Fin 2) (Fin 2) F) 1 0, 0, 0;
        -(X : Matrix (Fin 2) (Fin 2) F) 0 1, (X : Matrix (Fin 2) (Fin 2) F) 0 0, 0, 0;
        0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_transpose, WeakCT.coe_blockSL, blockMat_four_zero,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_block_qI_inv_transpose :
    ((((blockSL F 4 2 0 (by norm_num) (qI F))⁻¹).transpose : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = mI F := by
  rw [coe_block_inv_transpose]
  simp [qI]

theorem coe_block_qJ_inv_transpose (h3 : (3 : F) = 0) :
    ((((blockSL F 4 2 0 (by norm_num) (qJ h3))⁻¹).transpose : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = mJ' F := by
  rw [coe_block_inv_transpose]
  simp [qJ]

theorem trace_mI (h2 : (2 : F) ≠ 0) : (mI F).trace ≠ 0 := by
  simp only [Matrix.trace, Fin.sum_univ_four]
  simpa [one_add_one_eq_two] using h2

theorem trace_mJ (h2 : (2 : F) ≠ 0) : (mJ F).trace ≠ 0 := by
  simp only [Matrix.trace, Fin.sum_univ_four]
  simpa [one_add_one_eq_two] using h2

theorem trace_mJ' : (mJ' F).trace = (mJ F).trace := by
  simp only [Matrix.trace, Fin.sum_univ_four]
  simp

theorem eq_zero_of_eq_neg (h2 : (2 : F) ≠ 0) {a b : F} (h1 : a = b) (h1' : b = -a) : a = 0 :=
  (mul_eq_zero.mp (show (2 : F) * a = 0 by linear_combination h1 + h1')).resolve_left h2

theorem eq_of_comm_I (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F}
    (h : M * mI F = mI F * M) :
    M = !![M 0 0, M 0 1, 0, 0; -M 0 1, M 0 0, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
  have e : ∀ k l, (M * mI F) k l = (mI F * M) k l := fun k l => congrFun (congrFun h k) l
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e12 := e 1 2
  have e03 := e 0 3
  have e13 := e 1 3
  have e20 := e 2 0
  have e21 := e 2 1
  have e30 := e 3 0
  have e31 := e 3 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e12 e03 e13 e20 e21 e30 e31
  have h02 : M 0 2 = 0 := eq_zero_of_eq_neg h2 e02 (by linear_combination e12)
  have h12 : M 1 2 = 0 := by rw [← e02, h02]
  have h03 : M 0 3 = 0 := eq_zero_of_eq_neg h2 e03 (by linear_combination e13)
  have h13 : M 1 3 = 0 := by rw [← e03, h03]
  have h20 : M 2 0 = 0 := eq_zero_of_eq_neg h2 e21 (by linear_combination -e20)
  have h21 : M 2 1 = 0 := by rw [← e21, h20]
  have h30 : M 3 0 = 0 := eq_zero_of_eq_neg h2 e31 (by linear_combination -e30)
  have h31 : M 3 1 = 0 := by rw [← e31, h30]
  have h10 : M 1 0 = -M 0 1 := by linear_combination -e00
  have h11 : M 1 1 = M 0 0 := by linear_combination -e01
  ext k l
  fin_cases k <;> fin_cases l <;> simp [h02, h12, h03, h13, h20, h21, h30, h31, h10, h11]

theorem eq_of_comm_IJ (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F}
    (hi : M * mI F = mI F * M) (hj : M * mJ F = mJ F * M) :
    M = blk (M 0 0) (M 2 2) (M 2 3) (M 3 2) (M 3 3) := by
  have hM := eq_of_comm_I h2 hi
  have e := congrFun (congrFun hj 0) 0
  rw [hM] at e
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e
  have h01 : M 0 1 = 0 := eq_zero_of_eq_neg h2 rfl e
  rw [hM, h01]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

theorem eq_of_rel_dual (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F}
    (hi : M * mI F = mI F * M) (hj : M * mJ' F = mJ F * M) :
    M = blkJ (M 0 1) (M 2 2) (M 2 3) (M 3 2) (M 3 3) := by
  have hM := eq_of_comm_I h2 hi
  have e := congrFun (congrFun hj 0) 0
  rw [hM] at e
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e
  have h00 : M 0 0 = 0 := eq_zero_of_eq_neg h2 rfl e.symm
  rw [hM, h00]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

theorem comm_of_conjAut_fix {n : ℕ} (A : GL (Fin n) F) {r : SL(n, F)}
    (hr : conjAut n F A (proj n F r) = proj n F r)
    (htr : (r : Matrix (Fin n) (Fin n) F).trace ≠ 0) :
    (A : Matrix (Fin n) (Fin n) F) * r = r * A := by
  rw [conjAut_proj] at hr
  obtain ⟨c, -, hcm⟩ := proj_eq_exists hr
  rw [coe_slConjugation] at hcm
  have htrace := congrArg Matrix.trace hcm
  rw [Matrix.trace_smul, ModelFacts.Orth15.OuterL4.trace_conj, smul_eq_mul] at htrace
  have hc1 : (c : F) = 1 := by
    have h1 : (1 - (c : F)) * (r : Matrix (Fin n) (Fin n) F).trace = 0 := by
      linear_combination htrace
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right htr)).symm
  rw [hc1, one_smul] at hcm
  have hNA : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) F) * r =
      A * r * (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A) := by
        rw [hNA, Matrix.mul_one]
    _ = r * A := by rw [← Matrix.mul_assoc, ← hcm]

theorem rel_of_conjAut_dualAut_fix {n : ℕ} (A : GL (Fin n) F) {r : SL(n, F)}
    (hr : (conjAut n F A * dualAut n F) (proj n F r) = proj n F r)
    (htr : (((r⁻¹).transpose : SL(n, F)) : Matrix (Fin n) (Fin n) F).trace =
      (r : Matrix (Fin n) (Fin n) F).trace)
    (htr0 : (r : Matrix (Fin n) (Fin n) F).trace ≠ 0) :
    (A : Matrix (Fin n) (Fin n) F) * ((r⁻¹).transpose : SL(n, F)) = r * A := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at hr
  obtain ⟨c, -, hcm⟩ := proj_eq_exists hr
  rw [coe_slConjugation] at hcm
  have htrace := congrArg Matrix.trace hcm
  rw [Matrix.trace_smul, ModelFacts.Orth15.OuterL4.trace_conj, smul_eq_mul, htr] at htrace
  have hc1 : (c : F) = 1 := by
    have h1 : (1 - (c : F)) * (r : Matrix (Fin n) (Fin n) F).trace = 0 := by
      linear_combination htrace
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right htr0)).symm
  rw [hc1, one_smul] at hcm
  have hNA : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) F) * ((r⁻¹).transpose : SL(n, F)) =
      A * ((r⁻¹).transpose : SL(n, F)) *
        (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A) := by
        rw [hNA, Matrix.mul_one]
    _ = r * A := by rw [← Matrix.mul_assoc, ← hcm]

theorem conjAut_proj_eq_of_comm {n : ℕ} (A : GL (Fin n) F) (g : SL(n, F))
    (h : (A : Matrix (Fin n) (Fin n) F) * g = g * A) : conjAut n F A (proj n F g) = proj n F g := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem conjAut_dualAut_proj_eq {n : ℕ} (A : GL (Fin n) F) (g : SL(n, F))
    (h : (A : Matrix (Fin n) (Fin n) F) = g * A * (g : Matrix (Fin n) (Fin n) F)ᵀ) :
    (conjAut n F A * dualAut n F) (proj n F g) = proj n F g := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  have hgg : (g : Matrix (Fin n) (Fin n) F)ᵀ * ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  calc (A : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : Matrix (Fin n) (Fin n) F) * A * (g : Matrix (Fin n) (Fin n) F)ᵀ) *
        ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [← h]
    _ = (g : Matrix (Fin n) (Fin n) F) * ((A : Matrix (Fin n) (Fin n) F) *
        ((g : Matrix (Fin n) (Fin n) F)ᵀ * ((g⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        simp only [Matrix.mul_assoc]
    _ = g := by
        rw [hgg, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem exists_blk_of_comm [Finite F] (hF : Nat.card F = 3) {x : projectiveSL 4 F}
    (hx : ∀ y ∈ blockQ0 F, x * y = y * x) :
    ∃ g : SL(4, F), proj 4 F g = x ∧
      (g : Matrix (Fin 4) (Fin 4) F) = blk ((g : Matrix (Fin 4) (Fin 4) F) 0 0)
        ((g : Matrix (Fin 4) (Fin 4) F) 2 2) ((g : Matrix (Fin 4) (Fin 4) F) 2 3)
        ((g : Matrix (Fin 4) (Fin 4) F) 3 2) ((g : Matrix (Fin 4) (Fin 4) F) 3 3) := by
  have h2 := card3_two_ne_zero hF
  have h3 := card3_three_eq_zero hF
  obtain ⟨g, rfl⟩ := proj_surjective 4 F x
  have key : ∀ c ∈ commutator SL(2, F),
      conjAut 4 F (Matrix.SpecialLinearGroup.toGL g)
        (proj 4 F (blockSL F 4 2 0 (by norm_num) c)) =
        proj 4 F (blockSL F 4 2 0 (by norm_num) c) := fun c hc => by
    rw [LinearFlag.conjAut_toGL, MulAut.conj_apply, hx _ (mem_blockQ0 hc), mul_inv_cancel_right]
  have hI := comm_of_conjAut_fix _ (key _ (qI_mem hF)) (by rw [coe_block_qI]; exact trace_mI h2)
  have hJ := comm_of_conjAut_fix _ (key _ (qJ_mem hF h3))
    (by rw [coe_block_qJ]; exact trace_mJ h2)
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_block_qI] at hI
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_block_qJ] at hJ
  exact ⟨g, rfl, eq_of_comm_IJ h2 hI hJ⟩

theorem trace_eq_zero_of_inv {p q r s : F} (e00 : p * p + q * r = 1) (e01 : p * q + q * s = 0)
    (e10 : r * p + s * r = 0) (e11 : r * q + s * s = 1) (hns : ¬ (q = 0 ∧ r = 0 ∧ p = s)) :
    s = -p := by
  by_contra hne
  have hs : p + s ≠ 0 := fun h => hne (by linear_combination h)
  have hq : q = 0 :=
    (mul_eq_zero.mp (show q * (p + s) = 0 by linear_combination e01)).resolve_right hs
  have hr : r = 0 :=
    (mul_eq_zero.mp (show r * (p + s) = 0 by linear_combination e10)).resolve_right hs
  have hps : p = s := by
    have h1 : (p - s) * (p + s) = 0 := by
      rw [hq] at e00
      rw [hq] at e11
      linear_combination e00 - e11
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hs)
  exact hns ⟨hq, hr, hps⟩

theorem exists_conj_two (h2 : (2 : F) ≠ 0) {p q r s : F} (e00 : p * p + q * r = 1)
    (e01 : p * q + q * s = 0) (e10 : r * p + s * r = 0) (e11 : r * q + s * s = 1)
    (hns : ¬ (q = 0 ∧ r = 0 ∧ p = s)) :
    ∃ u v w t : F, u * t - v * w ≠ 0 ∧ p * u + q * w = u ∧ p * v + q * t = -v ∧
      r * u + s * w = w ∧ r * v + s * t = -t := by
  have htr := trace_eq_zero_of_inv e00 e01 e10 e11 hns
  subst htr
  by_cases hq : q = 0
  · subst hq
    have hp : (p - 1) * (p + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp hp with hp | hp
    · have hp1 : p = 1 := sub_eq_zero.mp hp
      subst hp1
      exact ⟨2, 0, r, 1, by simpa using h2, by ring, by ring, by ring, by ring⟩
    · have hp1 : p = -1 := eq_neg_of_add_eq_zero_left hp
      subst hp1
      exact ⟨0, 2, 1, -r, by simpa using h2, by ring, by ring, by ring, by ring⟩
  · refine ⟨q, q, 1 - p, -1 - p, fun h => hq ?_, by ring, by ring, ?_, ?_⟩
    · exact (mul_eq_zero.mp (show (2 : F) * q = 0 by linear_combination -h)).resolve_left h2
    · linear_combination e00
    · linear_combination e00

theorem dsq : blk (1 : F) 1 0 0 (-1) * blk 1 1 0 0 (-1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem coe_mk4 (M : Matrix (Fin 4) (Fin 4) F) (h : M.det ≠ 0) :
    ((GeneralLinearGroup.mkOfDetNeZero M h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = M :=
  rfl

@[expose] noncomputable def dGL (F : Type) [Field F] : GL (Fin 4) F :=
  ⟨blk 1 1 0 0 (-1), blk 1 1 0 0 (-1), dsq, dsq⟩

theorem coe_dGL : ((dGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk 1 1 0 0 (-1) := rfl

theorem conjAut_d_ne_conj [Finite F] (hF : Nat.card F = 3) (x : projectiveSL 4 F) :
    conjAut 4 F (dGL F) ≠ MulAut.conj x := by
  intro h
  have h2 := card3_two_ne_zero hF
  obtain ⟨g, rfl⟩ := proj_surjective 4 F x
  rw [← LinearFlag.conjAut_toGL] at h
  have h1 : conjAut 4 F (dGL F * (Matrix.SpecialLinearGroup.toGL g)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp h1
  have hdet := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F).det) hc
  have hg : ((Matrix.SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) F) =
      Matrix.SpecialLinearGroup.toGL g⁻¹ := (map_inv _ _).symm
  simp only [Units.val_mul, Matrix.det_mul, hg, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.det_coe, mul_one, coe_dGL, det_blk,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc2 := card3_mul_self hF c.ne_zero
  apply h2
  linear_combination (exp := 1) hdet - (1 + (c : F) * c) * hc2

theorem inv_mul_conj_mul {G : Type*} [Group G] (β : MulAut G) (x : G) :
    β⁻¹ * MulAut.conj x * β = MulAut.conj (β⁻¹ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.symm_apply_apply]

theorem ne_conj_of_eq [Finite F] (hF : Nat.card F = 3) {α : MulAut (projectiveSL 4 F)}
    {B : GL (Fin 4) F} (h : α = conjAut 4 F B * conjAut 4 F (dGL F) * (conjAut 4 F B)⁻¹)
    (x : projectiveSL 4 F) : α ≠ MulAut.conj x := by
  intro hx
  apply conjAut_d_ne_conj hF ((conjAut 4 F B)⁻¹ x)
  rw [← inv_mul_conj_mul, ← hx, h]
  group

theorem conjAut_blk_fix (u v w t : F) (hB : (blk 1 u v w t).det ≠ 0) :
    ∀ x ∈ blockQ0 F,
      conjAut 4 F (GeneralLinearGroup.mkOfDetNeZero (blk 1 u v w t) hB) x = x := by
  rintro _ ⟨c, -, rfl⟩
  refine conjAut_proj_eq_of_comm _ _ ?_
  rw [coe_mk4]
  show _ * ((blockSL F 4 2 0 (by norm_num) c : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = _
  rw [WeakCT.coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem sig_psl4 [Finite F] (hF : Nat.card F = 3) (α : MulAut (projectiveSL 4 F))
    (hα2 : α * α = 1) (hfix : ∀ x ∈ blockQ0 F, α x = x)
    (hmov : ∃ x : projectiveSL 4 F, (∀ y ∈ blockQ0 F, x * y = y * x) ∧ α x ≠ x) :
    ∃ B : GL (Fin 4) F, (∀ x ∈ blockQ0 F, conjAut 4 F B x = x) ∧
      α = conjAut 4 F B * conjAut 4 F (dGL F) * (conjAut 4 F B)⁻¹ := by
  have h2 := card3_two_ne_zero hF
  have h3 := card3_three_eq_zero hF
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  rw [card3_ringEquiv hF σ, show fieldAut 4 F (RingEquiv.refl F) = 1 from map_one _,
    mul_one] at hαeq
  have hfI := hfix _ (mem_blockQ0 (qI_mem hF))
  have hfJ := hfix _ (mem_blockQ0 (qJ_mem hF h3))
  obtain ⟨x, hxc, hxα⟩ := hmov
  obtain ⟨g, rfl, hg⟩ := exists_blk_of_comm hF hxc
  set c₀ := (g : Matrix (Fin 4) (Fin 4) F) 0 0
  set k00 := (g : Matrix (Fin 4) (Fin 4) F) 2 2
  set k01 := (g : Matrix (Fin 4) (Fin 4) F) 2 3
  set k10 := (g : Matrix (Fin 4) (Fin 4) F) 3 2
  set k11 := (g : Matrix (Fin 4) (Fin 4) F) 3 3
  have hdg : c₀ * c₀ * (k00 * k11 - k01 * k10) = 1 := by
    rw [← det_blk, ← hg]
    exact g.2
  have hc₀ : c₀ ≠ 0 := by
    rintro h0
    rw [h0] at hdg
    simp at hdg
  have hk : k00 * k11 - k01 * k10 = 1 := by
    rw [card3_mul_self hF hc₀, one_mul] at hdg
    exact hdg
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hαeq
    subst hαeq
    have hAI := comm_of_conjAut_fix A hfI (by rw [coe_block_qI]; exact trace_mI h2)
    have hAJ := comm_of_conjAut_fix A hfJ (by rw [coe_block_qJ]; exact trace_mJ h2)
    rw [coe_block_qI] at hAI
    rw [coe_block_qJ] at hAJ
    obtain ⟨a, p, q, r, s, hA⟩ : ∃ a p q r s : F,
        (A : Matrix (Fin 4) (Fin 4) F) = blk a p q r s :=
      ⟨_, _, _, _, _, eq_of_comm_IJ h2 hAI hAJ⟩
    have hdA : a * a * (p * s - q * r) ≠ 0 := by
      rw [← det_blk, ← hA]
      exact det_ne_zero A
    have ha : a ≠ 0 := fun h0 => hdA (by rw [h0]; ring)
    have ha2 := card3_mul_self hF ha
    obtain ⟨c, hc⟩ := (RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) (A * A)).mp
      (by rw [map_mul]; exact hα2)
    have hAA : blk a p q r s * blk a p q r s = blk (c : F) c 0 0 c := by
      have h1 := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F)) hc
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hA] at h1
      rw [← h1, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_one_eq_blk]
    rw [blk_mul] at hAA
    obtain ⟨hc1, e00, e01, e10, e11⟩ := blk_inj hAA
    have hcc : (c : F) = 1 := by rw [← hc1, ha2]
    rw [hcc] at e00 e11
    by_cases hns : q = 0 ∧ r = 0 ∧ p = s
    ·
      exfalso
      apply hxα
      obtain ⟨hq, hr, hps⟩ := hns
      refine conjAut_proj_eq_of_comm A g ?_
      rw [hA, hg, blk_mul, blk_mul, hq, hr, hps]
      congr 1 <;> ring
    · have hns' : ¬ (a * q = 0 ∧ a * r = 0 ∧ a * p = a * s) := fun ⟨h1, h1', h1''⟩ =>
        hns ⟨(mul_eq_zero.mp h1).resolve_left ha, (mul_eq_zero.mp h1').resolve_left ha,
          mul_left_cancel₀ ha h1''⟩
      obtain ⟨u, v, w, t, hdet, f1, f2, f3, f4⟩ := exists_conj_two h2
        (p := a * p) (q := a * q) (r := a * r) (s := a * s)
        (by linear_combination (p * p + q * r) * ha2 + e00)
        (by linear_combination (p * q + q * s) * ha2 + e01)
        (by linear_combination (r * p + s * r) * ha2 + e10)
        (by linear_combination (r * q + s * s) * ha2 + e11) hns'
      have hB : (blk 1 u v w t).det ≠ 0 := by rw [det_blk]; simpa using hdet
      set B := GeneralLinearGroup.mkOfDetNeZero (blk 1 u v w t) hB with hBdef
      refine ⟨B, conjAut_blk_fix u v w t hB, ?_⟩
      have hAB : conjAut 4 F (A * B) = conjAut 4 F (B * dGL F) := by
        refine conjAut_eq_of_smul _ _ a ha ?_
        rw [Units.val_mul, Units.val_mul, hA, hBdef, coe_mk4,
          coe_dGL, blk_mul, blk_mul, smul_blk]
        refine blk_congr (by ring) ?_ ?_ ?_ ?_
        · linear_combination a * f1 - (p * u + q * w) * ha2
        · linear_combination a * f2 - (p * v + q * t) * ha2
        · linear_combination a * f3 - (r * u + s * w) * ha2
        · linear_combination a * f4 - (r * v + s * t) * ha2
      rw [map_mul, map_mul] at hAB
      exact eq_mul_inv_iff_mul_eq.mpr hAB
  ·
    rw [pow_one] at hαeq
    subst hαeq
    have hAI := rel_of_conjAut_dualAut_fix A hfI
      (by rw [coe_block_qI_inv_transpose, coe_block_qI]) (by rw [coe_block_qI]; exact trace_mI h2)
    have hAJ := rel_of_conjAut_dualAut_fix A hfJ
      (by rw [coe_block_qJ_inv_transpose, coe_block_qJ]; exact trace_mJ')
      (by rw [coe_block_qJ]; exact trace_mJ h2)
    rw [coe_block_qI_inv_transpose, coe_block_qI] at hAI
    rw [coe_block_qJ_inv_transpose, coe_block_qJ] at hAJ
    obtain ⟨b, p, q, r, s, hA⟩ : ∃ b p q r s : F,
        (A : Matrix (Fin 4) (Fin 4) F) = blkJ b p q r s :=
      ⟨_, _, _, _, _, eq_of_rel_dual h2 hAI hAJ⟩
    have hdA : b * b * (p * s - q * r) ≠ 0 := by
      rw [← det_blkJ, ← hA]
      exact det_ne_zero A
    have hb : b ≠ 0 := fun h0 => hdA (by rw [h0]; ring)
    have hsq : (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F A * dualAut 4 F) =
        conjAut 4 F (A * Matrix.GeneralLinearGroup.inverseTranspose A) := by
      obtain ⟨-, -, -, hdd, -⟩ := standard_automorphism_transport (n := 4) (K := F)
      calc (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F A * dualAut 4 F)
          = conjAut 4 F A * (dualAut 4 F * conjAut 4 F A) * dualAut 4 F := by
            simp only [mul_assoc]
        _ = conjAut 4 F A * conjAut 4 F (Matrix.GeneralLinearGroup.inverseTranspose A) *
            (dualAut 4 F * dualAut 4 F) := by
            rw [dualAut_mul_conjAut]
            simp only [mul_assoc]
        _ = _ := by rw [hdd, mul_one, map_mul]
    obtain ⟨c, hc⟩ := (RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp
      (hsq ▸ hα2)
    have hAT : (A : Matrix (Fin 4) (Fin 4) F) = (c : F) • (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by
      have h1 := congrArg (fun X : GL (Fin 4) F =>
        (X : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F)ᵀ) hc
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose] at h1
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.transpose_one, Matrix.mul_one,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul] at h1
      exact h1.symm
    rw [hA] at hAT
    have t01 := congrFun (congrFun hAT 0) 1
    have t22 := congrFun (congrFun hAT 2) 2
    have t33 := congrFun (congrFun hAT 3) 3
    have t23 := congrFun (congrFun hAT 2) 3
    simp at t01 t22 t33 t23
    have hc1 : (c : F) = -1 := by
      have h1 : (1 + (c : F)) * b = 0 := by linear_combination t01
      linear_combination (mul_eq_zero.mp h1).resolve_right hb
    rw [hc1] at t22 t33 t23
    have hp : p = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination t22)
    have hs : s = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination t33)
    have hq : q = -r := by linear_combination t23
    exfalso
    apply hxα
    refine conjAut_dualAut_proj_eq A g ?_
    have hc02 := card3_mul_self hF hc₀
    rw [hA, hg, hp, hs, hq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;>
      first
      | ring1
      | linear_combination b * hc02
      | linear_combination (-b) * hc02
      | linear_combination r * hk
      | linear_combination (-r) * hk

end CFSG.ClassicalInvolution.Q3.TL4.E1521
