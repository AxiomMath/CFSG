module

public import CFSG.ClassicalInvolution.RouteD.SCRSp4Base

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg.Sp TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def Ad (d : F) (hd : d ≠ 0) : SL(2, F) :=
  ⟨!![0, -d; d⁻¹, 0], by simp [Matrix.det_fin_two, hd]⟩

theorem coe_Ad (d : F) (hd : d ≠ 0) : ((Ad d hd : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![0, -d; d⁻¹, 0] := rfl

theorem exists_conj_Ad (hn : ¬ IsSquare (-1 : F)) (B : SL(2, F))
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = -1) :
    ∃ (h : SL(2, F)) (d : F) (hd : d ≠ 0), h * B * h⁻¹ = Ad d hd := by
  have e00 := congrFun (congrFun hB 0) 0
  have e01 := congrFun (congrFun hB 0) 1
  have e10 := congrFun (congrFun hB 1) 0
  have e11 := congrFun (congrFun hB 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq] at e00 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] at e01 e10
  simp at e00 e11 e01 e10
  set a := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set c := (B : Matrix (Fin 2) (Fin 2) F) 0 1 with hc
  set D := (B : Matrix (Fin 2) (Fin 2) F) 1 0 with hD
  set b11 := (B : Matrix (Fin 2) (Fin 2) F) 1 1 with hb11
  have hD0 : D ≠ 0 := by
    intro h0
    apply hn
    refine ⟨a, ?_⟩
    rw [h0] at e00
    linear_combination -e00
  have hb : b11 = -a := by
    have : D * (a + b11) = 0 := by linear_combination e10
    have := (mul_eq_zero.mp this).resolve_left hD0
    linear_combination this
  let h : SL(2, F) := ⟨!![D, -a; 0, D⁻¹], by simp [Matrix.det_fin_two, hD0]⟩
  refine ⟨h, D, hD0, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_Ad]
  have hBm : (B : Matrix (Fin 2) (Fin 2) F) = !![a, c; D, b11] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hBm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h, Matrix.mul_apply, Fin.sum_univ_two, hb]
  all_goals first
    | (left; ring1)
    | linear_combination D * e00
    | ring1
    | field_simp


@[expose] def Dι (ι : F) (hι : ι * ι = -1) : SL(2, F) :=
  ⟨!![ι, 0; 0, -ι], by simp [Matrix.det_fin_two]; linear_combination -hι⟩

theorem coe_Dι (ι : F) (hι : ι * ι = -1) : ((Dι ι hι : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![ι, 0; 0, -ι] := rfl

@[expose] def Wl (F : Type) [Field F] : SL(2, F) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_Wl : ((Wl F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl

theorem sq_entries (B : SL(2, F)) (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = -1) :
    (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) F) 0 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 0 = -1 ∧
      (B : Matrix (Fin 2) (Fin 2) F) 1 0 * ((B : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 ∧
      (B : Matrix (Fin 2) (Fin 2) F) 0 1 * ((B : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (B : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 ∧
      (B : Matrix (Fin 2) (Fin 2) F) 1 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 1 +
        (B : Matrix (Fin 2) (Fin 2) F) 1 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 := by
  have e00 := congrFun (congrFun hB 0) 0
  have e01 := congrFun (congrFun hB 0) 1
  have e10 := congrFun (congrFun hB 1) 0
  have e11 := congrFun (congrFun hB 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨e00, ?_, ?_, e11⟩
  · linear_combination e10
  · linear_combination e01


theorem exists_conj_Dι_of_ne {ι : F} (hι : ι * ι = -1) (h2 : (2 : F) ≠ 0) (B : SL(2, F))
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = -1)
    (hD : (B : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : ∃ h : SL(2, F), h * B * h⁻¹ = Dι ι hι := by
  obtain ⟨e00, e10, e01, e11⟩ := sq_entries B hB
  set a := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set c := (B : Matrix (Fin 2) (Fin 2) F) 0 1 with hc
  set D := (B : Matrix (Fin 2) (Fin 2) F) 1 0 with hD'
  set b11 := (B : Matrix (Fin 2) (Fin 2) F) 1 1 with hb11
  have hb : b11 = -a := by
    have := (mul_eq_zero.mp e10).resolve_left hD
    linear_combination this
  have hι0 : ι ≠ 0 := by
    intro h0
    rw [h0] at hι
    simp at hι
  have hκ : 2 * ι * D ≠ 0 := mul_ne_zero (mul_ne_zero h2 hι0) hD
  let P : SL(2, F) := ⟨!![a + ι, (a - ι) * (2 * ι * D)⁻¹; D, D * (2 * ι * D)⁻¹], by
    simp only [Matrix.det_fin_two_of]
    field_simp
    ring⟩
  have hBP : B * P = P * Dι ι hι := by
    apply Subtype.ext
    have hBm : (B : Matrix (Fin 2) (Fin 2) F) = !![a, c; D, b11] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hBm, coe_Dι]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two, hb]
    all_goals first
      | ring1
      | linear_combination e00 - hι
      | linear_combination (D⁻¹ * (ι⁻¹ * 2⁻¹)) * (e00 - hι)
  refine ⟨P⁻¹, ?_⟩
  rw [inv_inv]
  calc P⁻¹ * B * P = P⁻¹ * (B * P) := by group
    _ = P⁻¹ * (P * Dι ι hι) := by rw [hBP]
    _ = Dι ι hι := by group


theorem coe_conj_Wl (B : SL(2, F)) :
    ((Wl F * B * (Wl F)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(B : Matrix (Fin 2) (Fin 2) F) 1 1, -(B : Matrix (Fin 2) (Fin 2) F) 1 0;
        -(B : Matrix (Fin 2) (Fin 2) F) 0 1, (B : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_Wl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem exists_conj_Dι {ι : F} (hι : ι * ι = -1) (h2 : (2 : F) ≠ 0) (B : SL(2, F))
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = -1) : ∃ h : SL(2, F), h * B * h⁻¹ = Dι ι hι := by
  by_cases hD : (B : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0
  · exact exists_conj_Dι_of_ne hι h2 B hB hD
  push Not at hD
  obtain ⟨e00, e10, e01, e11⟩ := sq_entries B hB
  by_cases hc : (B : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0
  · have hB' : ((Wl F * B * (Wl F)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((Wl F * B * (Wl F)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
      rw [coe_conj_Wl]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination e11
      · linear_combination -e10
      · linear_combination -e01
      · linear_combination e00
    have hD' : ((Wl F * B * (Wl F)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      rw [coe_conj_Wl]
      simpa using hc
    obtain ⟨h', hh'⟩ := exists_conj_Dι_of_ne hι h2 _ hB' hD'
    exact ⟨h' * Wl F, by simpa [mul_assoc] using hh'⟩
  push Not at hc
  have hdet : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (B : Matrix (Fin 2) (Fin 2) F) 0 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := B.2
    rw [Matrix.det_fin_two] at this
    exact this
  rw [hD, hc] at e00 hdet
  have ha2 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := by
    linear_combination e00
  have hb : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = -(B : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have ha0 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      rw [h0] at ha2
      simp at ha2
    have : (B : Matrix (Fin 2) (Fin 2) F) 0 0 *
        ((B : Matrix (Fin 2) (Fin 2) F) 1 1 + (B : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      linear_combination hdet + ha2
    have := (mul_eq_zero.mp this).resolve_left ha0
    linear_combination this
  have hBm : (B : Matrix (Fin 2) (Fin 2) F) =
      !![(B : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, -(B : Matrix (Fin 2) (Fin 2) F) 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, hc, hb]
  have hfac : ((B : Matrix (Fin 2) (Fin 2) F) 0 0 - ι) * ((B : Matrix (Fin 2) (Fin 2) F) 0 0 + ι) =
      0 := by
    linear_combination ha2 - hι
  rcases mul_eq_zero.mp hfac with h | h
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    have h' : (B : Matrix (Fin 2) (Fin 2) F) 0 0 = ι := by linear_combination h
    simp only [inv_one, mul_one, one_mul, coe_Dι]
    rw [hBm, h']
  · refine ⟨Wl F, ?_⟩
    apply Subtype.ext
    have h' : (B : Matrix (Fin 2) (Fin 2) F) 0 0 = -ι := by linear_combination h
    rw [coe_conj_Wl, coe_Dι]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, hc, hb, h']

end CFSG.ClassicalInvolution.RouteD.SCRSp4
