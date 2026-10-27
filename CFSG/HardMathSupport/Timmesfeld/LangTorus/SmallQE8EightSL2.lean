module

public import CFSG.RankThree.Classical.SL2SemilinearRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

open CFSG.RankThree.Classical
open scoped MatrixGroups Matrix

theorem eq_one_of_conjSL_diagUnitOne_fixed {F : Type} [Field F] [CharP F 2] (t : Fˣ)
    (C : SL(2, F)) (hC1 : C ≠ 1) (hCC : C * C = 1) (h : conjSL (diagUnitOne t) C = C) :
    t = 1 := by
  obtain ⟨a, b, c, d, hX⟩ : ∃ a b c d : F, (C : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := C.2
    rw [hX, Matrix.det_fin_two_of] at this
    exact this
  have hsq : (!![a, b; c, d] * !![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg Subtype.val hCC
    rw [Matrix.SpecialLinearGroup.coe_mul, hX, Matrix.SpecialLinearGroup.coe_one] at this
    exact this
  have haa : a * a + b * c = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hmat := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
  simp only [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv, hX] at hmat
  have hb : (t : F) * b = b := by
    have := congrFun (congrFun hmat 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at this
    exact this
  have hc : (t : F)⁻¹ * c = c := by
    have := congrFun (congrFun hmat 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, Units.val_inv_eq_inv_val] at this
    rw [mul_comm]
    exact this
  rcases eq_one_of_conj_fixed (t : F) a b c d hdet haa hb hc with h1 | ⟨ha, hb0, hc0, hd⟩
  · exact Units.ext h1
  · exfalso
    apply hC1
    apply Subtype.ext
    rw [hX, ha, hb0, hc0, hd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

end
