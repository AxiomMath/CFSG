module

public import CFSG.GH74.GLS.Stage4.HexSL2Defs

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex

variable {F : Type} [Field F]

@[expose] def negOne (F : Type) [Field F] : SL2 F := ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_negOne : (negOne F : Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, -1] := rfl

@[expose] def slConj (g : GL (Fin 2) F) : SL2 F →* SL2 F where
  toFun x := ⟨(g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
      have h1 : (g : Matrix (Fin 2) (Fin 2) F).det * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det
          = 1 := by
        rw [← Matrix.det_mul]
        simp
      rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, h1]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have h : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      simp
    show (g : Matrix (Fin 2) (Fin 2) F) * ((x * y : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
      ((g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h2 : ((g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
      ((g : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) *
        (y : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      simp only [Matrix.mul_assoc]
    rw [h2, h, Matrix.mul_one]
    simp only [Matrix.mul_assoc]

theorem coe_slConj (g : GL (Fin 2) F) (x : SL2 F) :
    (slConj g x : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] def diagGL (a b : Fˣ) : GL (Fin 2) F :=
  ⟨!![(a : F), 0; 0, (b : F)], !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[simp] theorem coe_diagGL (a b : Fˣ) :
    (diagGL a b : GL (Fin 2) F) = (!![(a : F), 0; 0, (b : F)] : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] def dNeg (F : Type) [Field F] : GL (Fin 2) F := diagGL 1 (-1)

@[expose] def uSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
    (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    rintro x y ⟨hx00, hx11, hx10⟩ ⟨hy00, hy11, hy10⟩
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx00, hx11, hx10,
      hy00, hy11, hy10]
  one_mem' := by simp
  inv_mem' := by
    rintro x ⟨hx00, hx11, hx10⟩
    have h := x.2
    rw [Matrix.det_fin_two, hx00, hx11, hx10] at h
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hx00, hx11, hx10]

@[expose] def lSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
    (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
  mul_mem' := by
    rintro x y ⟨hx00, hx11, hx01⟩ ⟨hy00, hy11, hy01⟩
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx00, hx11, hx01,
      hy00, hy11, hy01]
  one_mem' := by simp
  inv_mem' := by
    rintro x ⟨hx00, hx11, hx01⟩
    have h := x.2
    rw [Matrix.det_fin_two, hx00, hx11, hx01] at h
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hx00, hx11, hx01]

@[expose] def tSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    rintro x y ⟨hx01, hx10⟩ ⟨hy01, hy10⟩
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx01, hx10, hy01,
      hy10]
  one_mem' := by simp
  inv_mem' := by
    rintro x ⟨hx01, hx10⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hx01, hx10]

end CFSG.GH74.GLS.Stage4.Rest.T2
