module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixPfaffian

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

@[expose] def sixGram (F : Type*) [CommRing F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem sixGram_transpose (F : Type*) [CommRing F] :
    (sixGram F).transpose = sixGram F := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sixGram_square (F : Type*) [CommRing F] :
    sixGram F * sixGram F = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sixGram, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sixGram_det (F : Type*) [CommRing F] : (sixGram F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [sixGram, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]

@[expose] def sixGramGL (F : Type*) [CommRing F] : GL (Fin 4) F :=
  ⟨sixGram F, sixGram F, sixGram_square F, sixGram_square F⟩

variable {K : Type u} [Field K]

@[expose] def sixBar (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    Matrix (Fin 4) (Fin 4) (extension delta) := X.map (conjugation delta)

theorem sixBar_apply (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta))
    (i j : Fin 4) : sixBar delta X i j = conjugation delta (X i j) := rfl

theorem sixBar_add (delta : K) (X Y : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta (X + Y) = sixBar delta X + sixBar delta Y := by
  apply Matrix.ext
  intro i j
  exact map_add (conjugation delta) _ _

theorem sixBar_neg (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta (-X) = -sixBar delta X := by
  apply Matrix.ext
  intro i j
  exact map_neg (conjugation delta) _

theorem sixBar_mul (delta : K) (X Y : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta (X * Y) = sixBar delta X * sixBar delta Y := by
  exact Matrix.map_mul

theorem sixBar_transpose (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta X.transpose = (sixBar delta X).transpose := rfl

theorem sixBar_square (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta (sixBar delta X) = X := by
  apply Matrix.ext
  intro i j
  exact star_star _

theorem sixBar_smul (delta a : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta (a • X) = a • sixBar delta X := by
  apply Matrix.ext
  intro i j
  exact (conjugation delta).toLinearEquiv.map_smul a (X i j)

theorem sixBar_gram (delta : K) :
    sixBar delta (sixGram (extension delta)) = sixGram (extension delta) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sixBar, sixGram]

theorem sharp_base_smul (delta a : K)
    (X : Matrix (Fin 4) (Fin 4) (extension delta)) : sharp (a • X) = a • sharp X := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sharp, skewMatrix, smul_neg]

theorem sixBar_sharp (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixBar delta (sharp X) = sharp (sixBar delta X) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sixBar, sharp, skewMatrix]

@[expose] def sixSubmodule (delta : K) :
    Submodule K (Matrix (Fin 4) (Fin 4) (extension delta)) where
  carrier := {X | X.transpose = -X ∧
    sharp X = sixGram (extension delta) * sixBar delta X * sixGram (extension delta)}
  zero_mem' := by
    constructor
    · simp
    · apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [sharp, skewMatrix, sixBar]
  add_mem' {X} {Y} hX hY := by
    constructor
    · rw [Matrix.transpose_add, hX.1, hY.1, neg_add]
    · rw [sharp_add, hX.2, hY.2, sixBar_add, mul_add, add_mul]
  smul_mem' a X hX := by
    constructor
    · rw [Matrix.transpose_smul, hX.1, smul_neg]
    · rw [sharp_base_smul, hX.2, sixBar_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_sixSubmodule (delta : K)
    (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    X ∈ sixSubmodule delta ↔ X.transpose = -X ∧
      sharp X = sixGram (extension delta) * sixBar delta X * sixGram (extension delta) :=
  Iff.rfl

theorem extension_two_ne_zero (delta : K) (h2 : (2 : K) ≠ 0) :
    (2 : extension delta) ≠ 0 := by
  intro h
  apply h2
  apply QuadraticAlgebra.algebraMap_injective (a := delta) (b := 0)
  rw [map_ofNat, map_zero]
  exact h

theorem sixGram_skewMatrix {F : Type*} [CommRing F] (a b c d e f : F) :
    sixGram F * skewMatrix a b c d e f * sixGram F =
      skewMatrix f (-b) (-d) (-c) (-e) a := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sixGram, skewMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sixBar_skewMatrix (delta : K) (a b c d e f : extension delta) :
    sixBar delta (skewMatrix a b c d e f) =
      skewMatrix (conjugation delta a) (conjugation delta b) (conjugation delta c)
        (conjugation delta d) (conjugation delta e) (conjugation delta f) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sixBar, skewMatrix]

theorem six_entries (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) :
    conjugation delta (X.val 0 1) = X.val 0 1 ∧
      conjugation delta (X.val 2 3) = X.val 2 3 ∧
      X.val 1 3 = conjugation delta (X.val 0 2) ∧
      conjugation delta (X.val 0 3) = -X.val 0 3 ∧
      conjugation delta (X.val 1 2) = -X.val 1 2 := by
  have hx := X.property.2
  rw [skew_eq_skewMatrix (X := X.val) (extension_two_ne_zero delta h2) X.property.1,
    sixBar_skewMatrix, sixGram_skewMatrix] at hx
  have ha := congrArg (fun M => M 2 3) hx
  have hf := congrArg (fun M => M 0 1) hx
  have hb := congrArg (fun M => M 0 2) hx
  have hc := congrArg (fun M => M 1 2) hx
  have hd := congrArg (fun M => M 0 3) hx
  change X.val 0 3 = -conjugation delta (X.val 0 3) at hc
  change X.val 1 2 = -conjugation delta (X.val 1 2) at hd
  refine ⟨ha.symm, hf.symm, ?_, ?_, ?_⟩
  · exact neg_injective hb
  · exact neg_eq_iff_eq_neg.mp hc.symm
  · exact neg_eq_iff_eq_neg.mp hd.symm

theorem conjugation_anti_fixed_iff (delta : K) (h2 : (2 : K) ≠ 0)
    (z : extension delta) : conjugation delta z = -z ↔ z.re = 0 := by
  constructor
  · intro h
    have hr : z.re = -z.re := by
      simpa [conjugation] using congrArg QuadraticAlgebra.re h
    have hm : (2 : K) * z.re = 0 := by linear_combination hr
    exact (mul_eq_zero.mp hm).resolve_left h2
  · intro h
    apply QuadraticAlgebra.ext <;> simp [conjugation, h]

@[expose] def sixCoordinateMatrix (delta : K) (x : Fin 6 → K) :
    Matrix (Fin 4) (Fin 4) (extension delta) :=
  skewMatrix (algebraMap K (extension delta) (x 0)) ⟨x 2, x 3⟩
    ⟨0, x 4⟩ ⟨0, x 5⟩ (conjugation delta ⟨x 2, x 3⟩)
      (algebraMap K (extension delta) (x 1))

theorem sixCoordinateMatrix_mem (delta : K) (x : Fin 6 → K) :
    sixCoordinateMatrix delta x ∈ sixSubmodule delta := by
  constructor
  · exact skewMatrix_transpose _ _ _ _ _ _
  · rw [sixCoordinateMatrix, sharp_skewMatrix, sixBar_skewMatrix, sixGram_skewMatrix]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [skewMatrix, conjugation]

theorem six_original_coordinates (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (X : sixSubmodule delta) :
    X.val = sixCoordinateMatrix delta
      ![(X.val 0 1).re, (X.val 2 3).re, (X.val 0 2).re,
        (X.val 0 2).im, (X.val 0 3).im, (X.val 1 2).im] := by
  obtain ⟨ha, hf, hb, hc, hd⟩ := six_entries delta h2 X
  have ha' := (conjugation_fixed_iff delta h2 _).mp ha
  have hf' := (conjugation_fixed_iff delta h2 _).mp hf
  have hc' := (conjugation_anti_fixed_iff delta h2 _).mp hc
  have hd' := (conjugation_anti_fixed_iff delta h2 _).mp hd
  have hc'' : X.val 0 3 = ⟨0, (X.val 0 3).im⟩ := by
    apply QuadraticAlgebra.ext <;> simp [hc']
  have hd'' : X.val 1 2 = ⟨0, (X.val 1 2).im⟩ := by
    apply QuadraticAlgebra.ext <;> simp [hd']
  calc
    X.val = skewMatrix (X.val 0 1) (X.val 0 2) (X.val 0 3)
        (X.val 1 2) (X.val 1 3) (X.val 2 3) :=
      skew_eq_skewMatrix (extension_two_ne_zero delta h2) X.property.1
    _ = _ := by
      change skewMatrix _ _ _ _ _ _ = skewMatrix _ _ _ _ _ _
      rw [ha', hf', hc'', hd'', hb]
      rfl

theorem six_generator_coordinate (delta r : K) :
    (⟨0, r⟩ : extension delta) =
      QuadraticAlgebra.omega * algebraMap K (extension delta) r := by
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]

@[expose] def sixCoordinates (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    (Fin 6 → K) ≃ₗ[K] sixSubmodule delta where
  toFun x := ⟨sixCoordinateMatrix delta x, sixCoordinateMatrix_mem delta x⟩
  invFun X := ![(X.val 0 1).re, (X.val 2 3).re, (X.val 0 2).re,
    (X.val 0 2).im, (X.val 0 3).im, (X.val 1 2).im]
  left_inv x := by
    funext i
    fin_cases i <;> simp [sixCoordinateMatrix, skewMatrix]
  right_inv X := Subtype.ext (six_original_coordinates delta h2 X).symm
  map_add' x y := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sixCoordinateMatrix, skewMatrix, conjugation] <;>
      apply QuadraticAlgebra.ext <;> simp <;> ring
  map_smul' a x := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sixCoordinateMatrix, skewMatrix, conjugation, smul_neg] <;>
      apply QuadraticAlgebra.ext <;> simp [smul_eq_mul]

theorem sixCoordinates_val (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (x : Fin 6 → K) : (sixCoordinates delta h2 x).val = sixCoordinateMatrix delta x := rfl

theorem sixCoordinates_symm_apply (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) :
    (sixCoordinates delta h2).symm X =
      ![(X.val 0 1).re, (X.val 2 3).re, (X.val 0 2).re,
        (X.val 0 2).im, (X.val 0 3).im, (X.val 1 2).im] := rfl

theorem six_finrank (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    Module.finrank K (sixSubmodule delta) = 6 := by
  rw [← (sixCoordinates delta h2).finrank_eq]
  simp

@[expose] def sixForm (delta : K) : QuadraticForm K (sixSubmodule delta) :=
  let reEntry (i j : Fin 4) := ((QuadraticAlgebra.reₗ (a := delta) (b := 0)).comp
    (Matrix.entryLinearMap K (extension delta) i j)).comp (sixSubmodule delta).subtype
  let imEntry (i j : Fin 4) := ((QuadraticAlgebra.imₗ (a := delta) (b := 0)).comp
    (Matrix.entryLinearMap K (extension delta) i j)).comp (sixSubmodule delta).subtype
  linMulLin (reEntry 0 1) (reEntry 2 3) - linMulLin (reEntry 0 2) (reEntry 0 2) +
    delta • linMulLin (imEntry 0 2) (imEntry 0 2) +
      delta • linMulLin (imEntry 0 3) (imEntry 1 2)

theorem sixForm_apply (delta : K) (X : sixSubmodule delta) :
    sixForm delta X = (X.val 0 1).re * (X.val 2 3).re - (X.val 0 2).re ^ 2 +
      delta * (X.val 0 2).im ^ 2 + delta * (X.val 0 3).im * (X.val 1 2).im := by
  change (X.val 0 1).re * (X.val 2 3).re - (X.val 0 2).re * (X.val 0 2).re +
    delta * ((X.val 0 2).im * (X.val 0 2).im) +
      delta * ((X.val 0 3).im * (X.val 1 2).im) = _
  simp only [pow_two]
  ring

theorem sixForm_coordinates (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (x : Fin 6 → K) : sixForm delta (sixCoordinates delta h2 x) =
      x 0 * x 1 - x 2 ^ 2 + delta * x 3 ^ 2 + delta * x 4 * x 5 := by
  rw [sixForm_apply]
  rfl

theorem sixCoordinateMatrix_pfaffian (delta : K) (x : Fin 6 → K) :
    pfaffian (sixCoordinateMatrix delta x) =
      algebraMap K (extension delta)
        (x 0 * x 1 - x 2 ^ 2 + delta * x 3 ^ 2 + delta * x 4 * x 5) := by
  apply QuadraticAlgebra.ext <;>
    simp [sixCoordinateMatrix, pfaffian, skewMatrix, conjugation,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, pow_two] <;> ring

theorem sixForm_pfaffian (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (X : sixSubmodule delta) :
    algebraMap K (extension delta) (sixForm delta X) = pfaffian X.val := by
  rw [← (sixCoordinates delta h2).apply_symm_apply X, sixCoordinates_val,
    sixCoordinateMatrix_pfaffian, sixForm_coordinates]

theorem sixForm_polar (delta : K) (X Y : sixSubmodule delta) :
    (sixForm delta).polarBilin X Y =
      (X.val 0 1).re * (Y.val 2 3).re + (X.val 2 3).re * (Y.val 0 1).re -
      2 * (X.val 0 2).re * (Y.val 0 2).re +
      2 * delta * (X.val 0 2).im * (Y.val 0 2).im +
      delta * ((X.val 0 3).im * (Y.val 1 2).im + (X.val 1 2).im * (Y.val 0 3).im) := by
  rw [polarBilin_apply_apply, polar, sixForm_apply, sixForm_apply, sixForm_apply]
  simp only [Submodule.coe_add, Matrix.add_apply, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add]
  ring

theorem sixForm_nondegenerate (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    (sixForm delta).polarBilin.Nondegenerate := by
  have hn : ¬ IsSquare delta := Fact.out
  have hd : delta ≠ 0 := by rintro rfl; exact hn IsSquare.zero
  have left : (sixForm delta).polarBilin.SeparatingLeft := by
    intro X hX
    have h0 := hX (sixCoordinates delta h2 ![0, 1, 0, 0, 0, 0])
    have h1 := hX (sixCoordinates delta h2 ![1, 0, 0, 0, 0, 0])
    have h2' := hX (sixCoordinates delta h2 ![0, 0, 1, 0, 0, 0])
    have h3 := hX (sixCoordinates delta h2 ![0, 0, 0, 1, 0, 0])
    have h4 := hX (sixCoordinates delta h2 ![0, 0, 0, 0, 0, 1])
    have h5 := hX (sixCoordinates delta h2 ![0, 0, 0, 0, 1, 0])
    rw [sixForm_polar] at h0 h1 h2' h3 h4 h5
    have hz0 : (X.val 0 1).re = 0 := by
      simpa [sixCoordinates, sixCoordinateMatrix, skewMatrix, QuadraticAlgebra.re_one] using h0
    have hz1 : (X.val 2 3).re = 0 := by
      simpa [sixCoordinates, sixCoordinateMatrix, skewMatrix, QuadraticAlgebra.re_one] using h1
    have hz2 : (X.val 0 2).re = 0 := by
      have hm : (2 : K) * (X.val 0 2).re = 0 := by
        simpa [sixCoordinates, sixCoordinateMatrix, skewMatrix] using congrArg Neg.neg h2'
      exact (mul_eq_zero.mp hm).resolve_left h2
    have hz3 : (X.val 0 2).im = 0 := by
      have hm : (2 * delta) * (X.val 0 2).im = 0 := by
        simpa [sixCoordinates, sixCoordinateMatrix, skewMatrix] using h3
      exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero h2 hd)
    have hz4 : (X.val 0 3).im = 0 := by
      have hm : delta * (X.val 0 3).im = 0 := by
        simpa [sixCoordinates, sixCoordinateMatrix, skewMatrix] using h4
      exact (mul_eq_zero.mp hm).resolve_left hd
    have hz5 : (X.val 1 2).im = 0 := by
      have hm : delta * (X.val 1 2).im = 0 := by
        simpa [sixCoordinates, sixCoordinateMatrix, skewMatrix] using h5
      exact (mul_eq_zero.mp hm).resolve_left hd
    apply (sixCoordinates delta h2).symm.injective
    funext i
    fin_cases i <;> simpa [sixCoordinates] using (by assumption)
  refine ⟨left, ?_⟩
  intro X hX
  apply left X
  intro Y
  have h := hX Y
  rw [sixForm_polar] at h ⊢
  linear_combination h

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
