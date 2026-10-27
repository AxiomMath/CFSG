module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain Matrix

open scoped commutatorElement

private def sp4e0_xMat {F : Type} [Field F] (c d e : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, e, d, c; 0, 1, 0, d; 0, 0, 1, e; 0, 0, 0, 1]

private def sp4e0_hMat {F : Type} [Field F] (m : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, m 0 0, m 0 1, 0; 0, m 1 0, m 1 1, 0; 0, 0, 0, 1]

private lemma sp4e0_xMat_mul {F : Type} [Field F] (c d e c' d' e' : F) :
    sp4e0_xMat c d e * sp4e0_xMat c' d' e' =
      sp4e0_xMat (c + c' + e * d' + d * e') (d + d') (e + e') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_xMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma sp4e0_xMat_mul_self {F : Type} [Field F] [CharP F 2] (c d e : F) :
    sp4e0_xMat c d e * sp4e0_xMat c d e = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_xMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring_nf
  all_goals simp [h2]

private lemma sp4e0_hMat_mul {F : Type} [Field F] (m n : Matrix (Fin 2) (Fin 2) F) :
    sp4e0_hMat m * sp4e0_hMat n = sp4e0_hMat (m * n) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_hMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

private lemma sp4e0_hMat_one {F : Type} [Field F] :
    sp4e0_hMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp4e0_hMat]

private lemma sp4e0_sl2_det {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) :
    (m : Matrix (Fin 2) (Fin 2) F) 0 0 * (m : Matrix (Fin 2) (Fin 2) F) 1 1 +
      (m : Matrix (Fin 2) (Fin 2) F) 0 1 * (m : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h := m.2
  rw [Matrix.det_fin_two] at h
  linear_combination h + ((m : Matrix (Fin 2) (Fin 2) F) 0 1 *
    (m : Matrix (Fin 2) (Fin 2) F) 1 0) * h2

private lemma sp4e0_hMat_mul_inv {F : Type} [Field F] (m : Matrix.SpecialLinearGroup (Fin 2) F) :
    sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F) *
      sp4e0_hMat ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [sp4e0_hMat_mul]
  have h : (m : Matrix (Fin 2) (Fin 2) F) *
      ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    change ((m * m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    simp
  rw [h, sp4e0_hMat_one]

private lemma sp4e0_hMat_inv_mul {F : Type} [Field F] (m : Matrix.SpecialLinearGroup (Fin 2) F) :
    sp4e0_hMat ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [sp4e0_hMat_mul]
  have h : ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (m : Matrix (Fin 2) (Fin 2) F) = 1 := by
    change ((m⁻¹ * m : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    simp
  rw [h, sp4e0_hMat_one]

private noncomputable def sp4e0_xElt {F : Type} [Field F] [CharP F 2] (c d e : F) : GL (Fin 4) F :=
  Units.mk (sp4e0_xMat c d e) (sp4e0_xMat c d e)
    (sp4e0_xMat_mul_self c d e) (sp4e0_xMat_mul_self c d e)

private noncomputable def sp4e0_hElt {F : Type} [Field F]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) : GL (Fin 4) F :=
  Units.mk (sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F))
    (sp4e0_hMat ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (sp4e0_hMat_mul_inv m) (sp4e0_hMat_inv_mul m)

@[simp] private lemma sp4e0_xElt_coe {F : Type} [Field F] [CharP F 2] (c d e : F) :
    ((sp4e0_xElt c d e : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = sp4e0_xMat c d e :=
  rfl

@[simp] private lemma sp4e0_hElt_coe {F : Type} [Field F] (m : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((sp4e0_hElt m : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F) :=
  rfl

private def sp4e0_stab {F : Type} [Field F] : Subgroup (antiSp F) :=
  stabL (antiSp F).subtype (Pi.single (0 : Fin 4) (1 : F))

private lemma sp4e0_xElt_mem {F : Type} [Field F] [CharP F 2] (c d e : F) :
    sp4e0_xElt c d e ∈ antiSp F := by
  rw [mem_antiSp]
  change (sp4e0_xMat c d e)ᵀ * minorJ F * sp4e0_xMat c d e = minorJ F
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_xMat, mul_apply, Fin.sum_univ_four, minorJ_apply]
  all_goals ring_nf
  all_goals simp [h2]

private lemma sp4e0_hElt_mem {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) :
    sp4e0_hElt m ∈ antiSp F := by
  rw [mem_antiSp]
  change (sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F))ᵀ * minorJ F *
      sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F) = minorJ F
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hm := sp4e0_sl2_det m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_hMat, mul_apply, Fin.sum_univ_four, minorJ_apply]
  all_goals first
    | linear_combination hm
    | (ring_nf; simp [h2])

private lemma sp4e0_xMat_mulVec {F : Type} [Field F] (c d e : F) :
    sp4e0_xMat c d e *ᵥ (Pi.single (0 : Fin 4) (1 : F)) =
      Pi.single (0 : Fin 4) (1 : F) := by
  ext i
  fin_cases i <;> simp [sp4e0_xMat, Matrix.col_apply]

private lemma sp4e0_hMat_mulVec {F : Type} [Field F] (m : Matrix (Fin 2) (Fin 2) F) :
    sp4e0_hMat m *ᵥ (Pi.single (0 : Fin 4) (1 : F)) =
      Pi.single (0 : Fin 4) (1 : F) := by
  ext i
  fin_cases i <;> simp [sp4e0_hMat, Matrix.col_apply]

private noncomputable def sp4e0_xSub {F : Type} [Field F] [CharP F 2]
    (c d e : F) : antiSp F :=
  ⟨sp4e0_xElt c d e, sp4e0_xElt_mem c d e⟩

private noncomputable def sp4e0_hSub {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) : antiSp F :=
  ⟨sp4e0_hElt m, sp4e0_hElt_mem m⟩

private noncomputable def sp4e0_xS {F : Type} [Field F] [CharP F 2]
    (c d e : F) : sp4e0_stab (F := F) :=
  ⟨sp4e0_xSub c d e, by
    change ((sp4e0_xElt c d e : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
      (Pi.single (0 : Fin 4) (1 : F)) = Pi.single (0 : Fin 4) (1 : F)
    simpa using sp4e0_xMat_mulVec c d e⟩

private noncomputable def sp4e0_hS {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) : sp4e0_stab (F := F) :=
  ⟨sp4e0_hSub m, by
    change ((sp4e0_hElt m : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
      (Pi.single (0 : Fin 4) (1 : F)) = Pi.single (0 : Fin 4) (1 : F)
    simpa using sp4e0_hMat_mulVec (m : Matrix (Fin 2) (Fin 2) F)⟩

private lemma sp4e0_hMat_mul_xMat {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) (c d e : F) :
    sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F) * sp4e0_xMat c d e =
      sp4e0_xMat c ((m : Matrix (Fin 2) (Fin 2) F) 0 0 * d +
          (m : Matrix (Fin 2) (Fin 2) F) 0 1 * e)
        ((m : Matrix (Fin 2) (Fin 2) F) 1 0 * d +
          (m : Matrix (Fin 2) (Fin 2) F) 1 1 * e) *
        sp4e0_hMat (m : Matrix (Fin 2) (Fin 2) F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hm := sp4e0_sl2_det m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_hMat, sp4e0_xMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals (try (ring_nf; simp [h2]))
  case «0».«1» => linear_combination (-e) * hm
  case «0».«2» => linear_combination (-d) * hm

private lemma sp4e0_form_pres {F : Type} [Field F] (M : Matrix (Fin 4) (Fin 4) F)
    (hJ : Mᵀ * minorJ F * M = minorJ F) (x y : Fin 4 → F) :
    minorForm F (M *ᵥ x) (M *ᵥ y) = minorForm F x y := by
  have key : minorForm F (M *ᵥ x) (M *ᵥ y) =
      Matrix.toBilin' (Mᵀ * minorJ F * M) x y := by
    rw [← Matrix.toBilin'_comp]
    rfl
  rw [key, hJ]

private lemma sp4e0_decomp {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin 4) (Fin 4) F) (hJ : Mᵀ * minorJ F * M = minorJ F)
    (he0 : M *ᵥ (Pi.single (0 : Fin 4) (1 : F)) = Pi.single (0 : Fin 4) (1 : F)) :
    M = sp4e0_xMat (M 0 3) (M 1 3) (M 2 3) *
        sp4e0_hMat !![M 1 1, M 1 2; M 2 1, M 2 2] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpres := sp4e0_form_pres M hJ
  have hcol : ∀ i : Fin 4, M i 0 = (Pi.single (0 : Fin 4) (1 : F) : Fin 4 → F) i := by
    intro i
    have hcol0 : M.col (0 : Fin 4) = Pi.single (0 : Fin 4) (1 : F) := by
      rw [← Matrix.mulVec_single_one]; exact he0
    have := congrFun hcol0 i
    simpa [Matrix.col_apply] using this
  have hM00 : M 0 0 = 1 := by simpa using hcol 0
  have hM10 : M 1 0 = 0 := by simpa using hcol 1
  have hM20 : M 2 0 = 0 := by simpa using hcol 2
  have hlast : ∀ x : Fin 4 → F, (M *ᵥ x) 3 = x 3 := by
    intro x
    have h := hpres (Pi.single (0 : Fin 4) (1 : F)) x
    rw [he0] at h
    simpa [minorForm_apply] using h
  have hrow : ∀ i : Fin 4, M 3 i = (Pi.single i (1 : F) : Fin 4 → F) 3 := by
    intro i
    have := hlast (Pi.single i (1 : F))
    simpa [Matrix.mulVec_single_one] using this
  have hM30 : M 3 0 = 0 := by simpa using hrow 0
  have hM31 : M 3 1 = 0 := by simpa using hrow 1
  have hM32 : M 3 2 = 0 := by simpa using hrow 2
  have hM33 : M 3 3 = 1 := by simpa using hrow 3
  have h01 : M 0 1 = M 1 1 * M 2 3 + M 2 1 * M 1 3 := by
    have h := hpres (Pi.single (1 : Fin 4) (1 : F)) (Pi.single (3 : Fin 4) (1 : F))
    simp [minorForm_apply, Matrix.col_apply, minorJ_apply] at h
    rw [hM33, hM31] at h
    linear_combination h - (M 1 1 * M 2 3 + M 2 1 * M 1 3) * h2
  have h02 : M 0 2 = M 1 2 * M 2 3 + M 2 2 * M 1 3 := by
    have h := hpres (Pi.single (2 : Fin 4) (1 : F)) (Pi.single (3 : Fin 4) (1 : F))
    simp [minorForm_apply, Matrix.col_apply, minorJ_apply] at h
    rw [hM33, hM32] at h
    linear_combination h - (M 1 2 * M 2 3 + M 2 2 * M 1 3) * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4e0_xMat, sp4e0_hMat, Matrix.mul_apply, Fin.sum_univ_four,
      hM00, hM10, hM20, hM30, hM31, hM32, hM33, h01, h02]
  all_goals ring

private lemma sp4e0_middle_det {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin 4) (Fin 4) F) (hJ : Mᵀ * minorJ F * M = minorJ F)
    (he0 : M *ᵥ (Pi.single (0 : Fin 4) (1 : F)) = Pi.single (0 : Fin 4) (1 : F)) :
    (!![M 1 1, M 1 2; M 2 1, M 2 2] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpres := sp4e0_form_pres M hJ
  have hlast : ∀ x : Fin 4 → F, (M *ᵥ x) 3 = x 3 := by
    intro x
    have h := hpres (Pi.single (0 : Fin 4) (1 : F)) x
    rw [he0] at h
    simpa [minorForm_apply] using h
  have hM31 : M 3 1 = 0 := by
    have := hlast (Pi.single (1 : Fin 4) (1 : F))
    simpa [Matrix.mulVec_single_one] using this
  have hM32 : M 3 2 = 0 := by
    have := hlast (Pi.single (2 : Fin 4) (1 : F))
    simpa [Matrix.mulVec_single_one] using this
  have h := hpres (Pi.single (1 : Fin 4) (1 : F)) (Pi.single (2 : Fin 4) (1 : F))
  simp [minorForm_apply, Matrix.col_apply, minorJ_apply] at h
  rw [hM32, hM31] at h
  rw [Matrix.det_fin_two]
  change M 1 1 * M 2 2 - M 1 2 * M 2 1 = 1
  linear_combination h - (M 1 2 * M 2 1) * h2

private lemma sp4e0_exists_ne_zero_one {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have huniv : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := by
    intro a _
    by_cases h0 : a = 0
    · simp [h0]
    · simp [h a h0]
  have hcard : Fintype.card F ≤ 2 := by
    have := Finset.card_le_card huniv
    rw [Finset.card_univ] at this
    simpa using this
  have h4' : 4 ≤ Fintype.card F := by
    rwa [Nat.card_eq_fintype_card] at h4
  omega

private lemma sp4e0_sl2_perfect {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a, ha0, ha1⟩ := sp4e0_exists_ne_zero_one h4
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hsq0 : (a - 1) * (a - 1) = 0 := by
      linear_combination h + (1 - a) * h2
    exact ha1 (sub_eq_zero.mp (mul_self_eq_zero.mp hsq0))
  rw [Group.isPerfect_def]
  exact SL2.commutator_eq_top ha0 ha2

private noncomputable def sp4e0_torus {F : Type} [Field F] (lam : F) (hlam : lam ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![lam, 0; 0, lam⁻¹], by rw [Matrix.det_fin_two]; simp [hlam]⟩

private noncomputable def sp4e0_unip {F : Type} [Field F] (t : F) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

private lemma sp4e0_xElt_mul {F : Type} [Field F] [CharP F 2] (c d e c' d' e' : F) :
    sp4e0_xElt c d e * sp4e0_xElt c' d' e' =
      sp4e0_xElt (c + c' + e * d' + d * e') (d + d') (e + e') := by
  apply Units.ext
  simp only [sp4e0_xElt_coe, Units.val_mul]
  exact sp4e0_xMat_mul c d e c' d' e'

private lemma sp4e0_xElt_self {F : Type} [Field F] [CharP F 2] (c d e : F) :
    sp4e0_xElt c d e * sp4e0_xElt c d e = 1 := by
  apply Units.ext
  simp only [sp4e0_xElt_coe, Units.val_mul, Units.val_one]
  exact sp4e0_xMat_mul_self c d e

private lemma sp4e0_xSub_mul {F : Type} [Field F] [CharP F 2] (c d e c' d' e' : F) :
    sp4e0_xSub c d e * sp4e0_xSub c' d' e' =
      sp4e0_xSub (c + c' + e * d' + d * e') (d + d') (e + e') := by
  apply Subtype.ext
  simp only [sp4e0_xSub, Subtype.coe_mk, Subgroup.coe_mul]
  exact sp4e0_xElt_mul c d e c' d' e'

private lemma sp4e0_xSub_self {F : Type} [Field F] [CharP F 2] (c d e : F) :
    sp4e0_xSub c d e * sp4e0_xSub c d e = 1 := by
  apply Subtype.ext
  simp only [sp4e0_xSub, Subgroup.coe_mul]
  exact sp4e0_xElt_self c d e

private lemma sp4e0_xS_mul {F : Type} [Field F] [CharP F 2] (c d e c' d' e' : F) :
    sp4e0_xS c d e * sp4e0_xS c' d' e' =
      sp4e0_xS (c + c' + e * d' + d * e') (d + d') (e + e') := by
  apply Subtype.ext
  simp only [sp4e0_xS, Subtype.coe_mk, Subgroup.coe_mul]
  exact sp4e0_xSub_mul c d e c' d' e'

private lemma sp4e0_xS_self {F : Type} [Field F] [CharP F 2] (c d e : F) :
    sp4e0_xS c d e * sp4e0_xS c d e = 1 := by
  apply Subtype.ext
  simp only [sp4e0_xS, Subgroup.coe_mul]
  exact sp4e0_xSub_self c d e

private lemma sp4e0_xS_inv {F : Type} [Field F] [CharP F 2] (c d e : F) :
    (sp4e0_xS c d e)⁻¹ = sp4e0_xS c d e :=
  inv_eq_of_mul_eq_one_right (sp4e0_xS_self c d e)

private lemma sp4e0_hElt_mul_xElt {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) (c d e : F) :
    sp4e0_hElt m * sp4e0_xElt c d e =
      sp4e0_xElt c ((m : Matrix (Fin 2) (Fin 2) F) 0 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 0 1 * e)
          ((m : Matrix (Fin 2) (Fin 2) F) 1 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 1 1 * e) * sp4e0_hElt m := by
  apply Units.ext
  simpa only [sp4e0_hElt_coe, sp4e0_xElt_coe, Units.val_mul] using
    sp4e0_hMat_mul_xMat m c d e

private lemma sp4e0_hSub_mul_xSub {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) (c d e : F) :
    sp4e0_hSub m * sp4e0_xSub c d e =
      sp4e0_xSub c ((m : Matrix (Fin 2) (Fin 2) F) 0 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 0 1 * e)
          ((m : Matrix (Fin 2) (Fin 2) F) 1 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 1 1 * e) * sp4e0_hSub m := by
  apply Subtype.ext
  simp only [sp4e0_hSub, sp4e0_xSub, Subgroup.coe_mul]
  exact sp4e0_hElt_mul_xElt m c d e

private lemma sp4e0_hS_mul_xS {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) (c d e : F) :
    sp4e0_hS m * sp4e0_xS c d e =
      sp4e0_xS c ((m : Matrix (Fin 2) (Fin 2) F) 0 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 0 1 * e)
          ((m : Matrix (Fin 2) (Fin 2) F) 1 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 1 1 * e) * sp4e0_hS m := by
  apply Subtype.ext
  simp only [sp4e0_hS, sp4e0_xS, Subgroup.coe_mul]
  exact sp4e0_hSub_mul_xSub m c d e

private lemma sp4e0_hS_conj_xS {F : Type} [Field F] [CharP F 2]
    (m : Matrix.SpecialLinearGroup (Fin 2) F) (c d e : F) :
    sp4e0_hS m * sp4e0_xS c d e * (sp4e0_hS m)⁻¹ =
      sp4e0_xS c ((m : Matrix (Fin 2) (Fin 2) F) 0 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 0 1 * e)
          ((m : Matrix (Fin 2) (Fin 2) F) 1 0 * d +
            (m : Matrix (Fin 2) (Fin 2) F) 1 1 * e) := by
  rw [sp4e0_hS_mul_xS, mul_assoc, mul_inv_cancel, mul_one]

private lemma sp4e0_hElt_mul {F : Type} [Field F] (m n : Matrix.SpecialLinearGroup (Fin 2) F) :
    sp4e0_hElt (m * n) = sp4e0_hElt m * sp4e0_hElt n := by
  apply Units.ext
  simp only [sp4e0_hElt_coe, Units.val_mul]
  rw [sp4e0_hMat_mul]
  rfl

private lemma sp4e0_hS_one {F : Type} [Field F] [CharP F 2] :
    sp4e0_hS (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp only [sp4e0_hS, sp4e0_hSub, Subtype.coe_mk, sp4e0_hElt_coe]
  exact sp4e0_hMat_one

private lemma sp4e0_hS_mul {F : Type} [Field F] [CharP F 2]
    (m n : Matrix.SpecialLinearGroup (Fin 2) F) :
    sp4e0_hS (m * n) = sp4e0_hS m * sp4e0_hS n := by
  apply Subtype.ext
  apply Subtype.ext
  exact sp4e0_hElt_mul m n

private lemma sp4e0_comm_torus_e0 {F : Type} [Field F] [CharP F 2]
    (lam : F) (hlam : lam ≠ 0) (d : F) :
    ⁅sp4e0_hS (sp4e0_torus lam hlam), sp4e0_xS 0 d 0⁆ =
      sp4e0_xS 0 ((lam + 1) * d) 0 := by
  rw [commutatorElement_def, sp4e0_hS_conj_xS, sp4e0_xS_inv, sp4e0_xS_mul]
  congr 1 <;> simp [sp4e0_torus]
  ring_nf

private lemma sp4e0_comm_torus_0e {F : Type} [Field F] [CharP F 2]
    (lam : F) (hlam : lam ≠ 0) (e : F) :
    ⁅sp4e0_hS (sp4e0_torus lam hlam), sp4e0_xS 0 0 e⁆ =
      sp4e0_xS 0 0 ((lam⁻¹ + 1) * e) := by
  rw [commutatorElement_def, sp4e0_hS_conj_xS, sp4e0_xS_inv, sp4e0_xS_mul]
  congr 1 <;> simp [sp4e0_torus]
  ring_nf

private lemma sp4e0_comm_unip {F : Type} [Field F] [CharP F 2] (t : F) :
    ⁅sp4e0_hS (sp4e0_unip t), sp4e0_xS 0 0 1⁆ = sp4e0_xS t t 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, sp4e0_hS_conj_xS, sp4e0_xS_inv, sp4e0_xS_mul]
  congr 1 <;> simp [sp4e0_unip]
  ring_nf
  simp [h2]

private lemma sp4e0_hS_mem_commutator {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) (m : Matrix.SpecialLinearGroup (Fin 2) F) :
    (sp4e0_hS m : antiSp F) ∈ ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := sp4e0_sl2_perfect h4
  let psi : Matrix.SpecialLinearGroup (Fin 2) F →* sp4e0_stab (F := F) :=
    { toFun := sp4e0_hS
      map_one' := sp4e0_hS_one
      map_mul' := sp4e0_hS_mul }
  have hmem : sp4e0_hS m ∈ ⁅(⊤ : Subgroup (sp4e0_stab (F := F))),
      (⊤ : Subgroup (sp4e0_stab (F := F)))⁆ := by
    have hperf : psi.range = ⁅psi.range, psi.range⁆ :=
      (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range psi)).symm
    have hle : ⁅psi.range, psi.range⁆ ≤ ⁅(⊤ : Subgroup (sp4e0_stab (F := F))),
        (⊤ : Subgroup (sp4e0_stab (F := F)))⁆ :=
      Subgroup.commutator_mono le_top le_top
    exact hle (hperf ▸ ⟨m, rfl⟩)
  have hmap : Subgroup.map (sp4e0_stab (F := F)).subtype
      ⁅(⊤ : Subgroup (sp4e0_stab (F := F))), (⊤ : Subgroup (sp4e0_stab (F := F)))⁆ =
        ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  exact hmap ▸ Subgroup.mem_map_of_mem (sp4e0_stab (F := F)).subtype hmem

private lemma sp4e0_mem_of_mem_top_commutator {F : Type} [Field F] [CharP F 2]
    (x : sp4e0_stab (F := F)) (hx : x ∈ ⁅(⊤ : Subgroup (sp4e0_stab (F := F))),
      (⊤ : Subgroup (sp4e0_stab (F := F)))⁆) :
    (x : antiSp F) ∈ ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
  have hmap : Subgroup.map (sp4e0_stab (F := F)).subtype
      ⁅(⊤ : Subgroup (sp4e0_stab (F := F))), (⊤ : Subgroup (sp4e0_stab (F := F)))⁆ =
        ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  exact hmap ▸ Subgroup.mem_map_of_mem (sp4e0_stab (F := F)).subtype hx

private lemma sp4e0_xS_mem_commutator {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) (c d e : F) :
    (sp4e0_xS c d e : antiSp F) ∈ ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
  obtain ⟨lam, hlam0, hlam1⟩ := sp4e0_exists_ne_zero_one h4
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hlp1 : lam + 1 ≠ 0 := by
    intro h
    apply hlam1
    linear_combination h + (-1) * h2
  have hlpinv1 : lam⁻¹ + 1 ≠ 0 := by
    intro h
    apply hlam1
    have h1 : lam⁻¹ = 1 := by linear_combination h + (-1) * h2
    calc lam = (lam⁻¹)⁻¹ := (inv_inv lam).symm
      _ = 1 := by rw [h1, inv_one]
  have hd0 : ∀ d' : F, (sp4e0_xS 0 d' 0 : antiSp F) ∈
      ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
    intro d'
    have hcomp : (lam + 1) * (d' * (lam + 1)⁻¹) = d' := by
      rw [mul_comm d' (lam + 1)⁻¹, ← mul_assoc, mul_inv_cancel₀ hlp1, one_mul]
    have hcomm : ⁅sp4e0_hS (sp4e0_torus lam hlam0),
        sp4e0_xS 0 (d' * (lam + 1)⁻¹) 0⁆ = sp4e0_xS 0 d' 0 := by
      rw [sp4e0_comm_torus_e0, hcomp]
    refine sp4e0_mem_of_mem_top_commutator (sp4e0_xS 0 d' 0) ?_
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have he0 : ∀ e' : F, (sp4e0_xS 0 0 e' : antiSp F) ∈
      ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
    intro e'
    have hcomp : (lam⁻¹ + 1) * (e' * (lam⁻¹ + 1)⁻¹) = e' := by
      rw [mul_comm e' (lam⁻¹ + 1)⁻¹, ← mul_assoc, mul_inv_cancel₀ hlpinv1, one_mul]
    have hcomm : ⁅sp4e0_hS (sp4e0_torus lam hlam0),
        sp4e0_xS 0 0 (e' * (lam⁻¹ + 1)⁻¹)⁆ = sp4e0_xS 0 0 e' := by
      rw [sp4e0_comm_torus_0e, hcomp]
    refine sp4e0_mem_of_mem_top_commutator (sp4e0_xS 0 0 e') ?_
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have htt0 : ∀ t : F, (sp4e0_xS t t 0 : antiSp F) ∈
      ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
    intro t
    refine sp4e0_mem_of_mem_top_commutator (sp4e0_xS t t 0) ?_
    rw [← sp4e0_comm_unip t]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have ht00 : ∀ t : F, (sp4e0_xS t 0 0 : antiSp F) ∈
      ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ := by
    intro t
    have hprodS : sp4e0_xS t 0 0 = sp4e0_xS t t 0 * sp4e0_xS 0 t 0 := by
      apply Subtype.ext
      change sp4e0_xSub t 0 0 = sp4e0_xSub t t 0 * sp4e0_xSub 0 t 0
      rw [sp4e0_xSub_mul]
      apply Subtype.ext
      change sp4e0_xElt t 0 0 = sp4e0_xElt (t + 0 + 0 * t + t * 0) (t + t) (0 + 0)
      rw [show (t + 0 + 0 * t + t * 0 : F) = t from by ring,
          show (t + t : F) = 0 from by linear_combination t * h2,
          show (0 + 0 : F) = 0 from by ring]
    rw [hprodS]
    simpa using (⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆).mul_mem (htt0 t) (hd0 t)
  have hprodS : sp4e0_xS c d e =
      sp4e0_xS (c + d * e) 0 0 * sp4e0_xS 0 d 0 * sp4e0_xS 0 0 e := by
    apply Subtype.ext
    change sp4e0_xSub c d e =
      sp4e0_xSub (c + d * e) 0 0 * sp4e0_xSub 0 d 0 * sp4e0_xSub 0 0 e
    rw [sp4e0_xSub_mul, sp4e0_xSub_mul]
    apply Subtype.ext
    change sp4e0_xElt c d e =
      sp4e0_xElt (c + d * e + 0 + 0 * d + 0 * 0 + 0 + (0 + 0) * 0 + (0 + d) * e)
        (0 + d + 0) (0 + 0 + e)
    rw [show (c + d * e + 0 + 0 * d + 0 * 0 + 0 + (0 + 0) * 0 + (0 + d) * e : F) = c from by
          linear_combination (d * e) * h2,
        show (0 + d + 0 : F) = d from by ring,
        show (0 + 0 + e : F) = e from by ring]
  rw [hprodS]
  simpa using (⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆).mul_mem
    ((⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆).mul_mem (ht00 (c + d * e)) (hd0 d))
    (he0 e)

theorem sp4_perfect_stab_e0 {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    ⁅stabL (antiSp F).subtype (Pi.single (0 : Fin 4) (1 : F)),
        stabL (antiSp F).subtype (Pi.single (0 : Fin 4) (1 : F))⁆ =
      stabL (antiSp F).subtype (Pi.single (0 : Fin 4) (1 : F)) := by
  change ⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆ = sp4e0_stab (F := F)
  apply le_antisymm (Subgroup.commutator_le_self _)
  intro g hg
  have hgfix : (glMat (g : GL (Fin 4) F)) *ᵥ (Pi.single (0 : Fin 4) (1 : F)) =
      Pi.single (0 : Fin 4) (1 : F) := hg
  have hgJ : (glMat (g : GL (Fin 4) F))ᵀ * minorJ F * glMat (g : GL (Fin 4) F) = minorJ F :=
    g.2
  have hdecomp := sp4e0_decomp (glMat (g : GL (Fin 4) F)) hgJ hgfix
  have hdet : (!![(glMat (g : GL (Fin 4) F)) 1 1, (glMat (g : GL (Fin 4) F)) 1 2;
      (glMat (g : GL (Fin 4) F)) 2 1, (glMat (g : GL (Fin 4) F)) 2 2] :
        Matrix (Fin 2) (Fin 2) F).det = 1 :=
    sp4e0_middle_det (glMat (g : GL (Fin 4) F)) hgJ hgfix
  let mSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![(glMat (g : GL (Fin 4) F)) 1 1, (glMat (g : GL (Fin 4) F)) 1 2;
        (glMat (g : GL (Fin 4) F)) 2 1, (glMat (g : GL (Fin 4) F)) 2 2], hdet⟩
  have hge : g = (sp4e0_xS ((glMat (g : GL (Fin 4) F)) 0 3)
        ((glMat (g : GL (Fin 4) F)) 1 3) ((glMat (g : GL (Fin 4) F)) 2 3) *
        sp4e0_hS mSL : sp4e0_stab (F := F)) := by
    apply Subtype.ext
    apply Units.ext
    exact hdecomp
  rw [hge]
  simpa using (⁅sp4e0_stab (F := F), sp4e0_stab (F := F)⁆).mul_mem
    (sp4e0_xS_mem_commutator h4 _ _ _) (sp4e0_hS_mem_commutator h4 mSL)


end CFSG.LocalAnalysis.RankThreeUC.S15

end