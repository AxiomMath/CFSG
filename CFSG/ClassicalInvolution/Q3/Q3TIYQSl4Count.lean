module

public import CFSG.ClassicalInvolution.Q3.Q3TIYQSL

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.TG3
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

noncomputable def sl4U (a b c d : 𝔽₃) : SL(4, 𝔽₃) :=
  ⟨!![1, 0, a, b; 0, 1, c, d; 0, 0, 1, 0; 0, 0, 0, 1], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩

theorem sl4U_mul_neg (a b c d : 𝔽₃) : sl4U a b c d * sl4U (-a) (-b) (-c) (-d) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [sl4U, Matrix.mul_apply, Fin.sum_univ_four]

theorem sl4U_inv (a b c d : 𝔽₃) : (sl4U a b c d)⁻¹ = sl4U (-a) (-b) (-c) (-d) :=
  inv_eq_of_mul_eq_one_right (sl4U_mul_neg a b c d)

theorem negBlock_four_zero : (negBlock 𝔽₃ 4 0 : Matrix (Fin 4) (Fin 4) 𝔽₃) =
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem negBlock_four_two : (negBlock 𝔽₃ 4 2 : Matrix (Fin 4) (Fin 4) 𝔽₃) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rw [negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

noncomputable def sl4Inv0 (a b c d : 𝔽₃) : SL(4, 𝔽₃) :=
  sl4U a b c d * blockSL 𝔽₃ 4 2 0 (by omega) (-1) * (sl4U a b c d)⁻¹

noncomputable def sl4Inv1 (a b c d : 𝔽₃) : SL(4, 𝔽₃) :=
  sl4U a b c d * blockSL 𝔽₃ 4 2 2 (by omega) (-1) * (sl4U a b c d)⁻¹

theorem coe_sl4Inv0 (a b c d : 𝔽₃) : (sl4Inv0 a b c d : Matrix (Fin 4) (Fin 4) 𝔽₃) =
    !![-1, 0, 2 * a, 2 * b; 0, -1, 2 * c, 2 * d; 0, 0, 1, 0; 0, 0, 0, 1] := by
  unfold sl4Inv0
  rw [sl4U_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL_neg_one, negBlock_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl4U, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem coe_sl4Inv1 (a b c d : 𝔽₃) : (sl4Inv1 a b c d : Matrix (Fin 4) (Fin 4) 𝔽₃) =
    !![1, 0, -(2 * a), -(2 * b); 0, 1, -(2 * c), -(2 * d); 0, 0, -1, 0; 0, 0, 0, -1] := by
  unfold sl4Inv1
  rw [sl4U_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL_neg_one, negBlock_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl4U, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

noncomputable def sl4R0 (a b c d : 𝔽₃) : Subgroup SL(4, 𝔽₃) :=
  (blockSL 𝔽₃ 4 2 0 (by omega)).range.map (MulAut.conj (sl4U a b c d)).toMonoidHom

noncomputable def sl4R1 (a b c d : 𝔽₃) : Subgroup SL(4, 𝔽₃) :=
  (blockSL 𝔽₃ 4 2 2 (by omega)).range.map (MulAut.conj (sl4U a b c d)).toMonoidHom

theorem isLongRootSL2_sl4R0 (a b c d : 𝔽₃) :
    IsLongRootSL2 (show 2 ≤ 4 by norm_num) (sl4R0 a b c d) (sl4Inv0 a b c d) :=
  (isLongRootSL2_range_blockSL two_ne_zero_three (by omega : 0 + 2 ≤ 4)).conj (sl4U a b c d)

theorem isLongRootSL2_sl4R1 (a b c d : 𝔽₃) :
    IsLongRootSL2 (show 2 ≤ 4 by norm_num) (sl4R1 a b c d) (sl4Inv1 a b c d) :=
  (isLongRootSL2_range_blockSL two_ne_zero_three (by omega : 2 + 2 ≤ 4)).conj (sl4U a b c d)


theorem mem_fund_of_isLongRootSL2_four {R : Subgroup SL(4, 𝔽₃)} {i : SL(4, 𝔽₃)}
    (h : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R i) :
    R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D := by
  have hL := RouteD.Exotic.fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := 3) (by omega)
  have h' : R ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ 3 + 1) := ⟨i, h⟩
  rw [← hL] at h'
  exact h'

theorem card_fund_psl4_ge :
    162 ≤ Nat.card {R : Subgroup SL(4, 𝔽₃) //
      R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D} := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  let f : (𝔽₃ × 𝔽₃ × 𝔽₃ × 𝔽₃) ⊕ (𝔽₃ × 𝔽₃ × 𝔽₃ × 𝔽₃) →
      {R : Subgroup SL(4, 𝔽₃) //
        R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D} :=
    Sum.elim
      (fun p => ⟨sl4R0 p.1 p.2.1 p.2.2.1 p.2.2.2,
        mem_fund_of_isLongRootSL2_four (isLongRootSL2_sl4R0 _ _ _ _)⟩)
      (fun p => ⟨sl4R1 p.1 p.2.1 p.2.2.1 p.2.2.2,
        mem_fund_of_isLongRootSL2_four (isLongRootSL2_sl4R1 _ _ _ _)⟩)
  have hf : Function.Injective f := by
    rintro (⟨a, b, c, d⟩ | ⟨a, b, c, d⟩) (⟨a', b', c', d'⟩ | ⟨a', b', c', d'⟩) h
    · have hR : sl4R0 a b c d = sl4R0 a' b' c' d' := congrArg Subtype.val h
      have hi' : IsLongRootSL2 (show 2 ≤ 4 by norm_num) (sl4R0 a b c d)
          (sl4Inv0 a' b' c' d') := by
        rw [hR]
        exact isLongRootSL2_sl4R0 a' b' c' d'
      have hi := (isLongRootSL2_sl4R0 a b c d).involution_unique h2 hi'
      have hm := congrArg (fun A : SL(4, 𝔽₃) => (A : Matrix (Fin 4) (Fin 4) 𝔽₃)) hi
      simp only [coe_sl4Inv0] at hm
      have h02 : 2 * a = 2 * a' := congrFun (congrFun hm 0) 2
      have h03 : 2 * b = 2 * b' := congrFun (congrFun hm 0) 3
      have h12 : 2 * c = 2 * c' := congrFun (congrFun hm 1) 2
      have h13 : 2 * d = 2 * d' := congrFun (congrFun hm 1) 3
      rw [mul_left_cancel₀ h2 h02, mul_left_cancel₀ h2 h03, mul_left_cancel₀ h2 h12,
        mul_left_cancel₀ h2 h13]
    · exfalso
      have hR : sl4R0 a b c d = sl4R1 a' b' c' d' := congrArg Subtype.val h
      have hi := (isLongRootSL2_sl4R0 a b c d).involution_unique h2
        (hR ▸ isLongRootSL2_sl4R1 a' b' c' d')
      have hm := congrArg (fun A : SL(4, 𝔽₃) => (A : Matrix (Fin 4) (Fin 4) 𝔽₃)) hi
      simp only [coe_sl4Inv0, coe_sl4Inv1] at hm
      have h00 : (-1 : 𝔽₃) = 1 := congrFun (congrFun hm 0) 0
      have : (2 : 𝔽₃) = 0 := by linear_combination -h00
      exact h2 this
    · exfalso
      have hR : sl4R1 a b c d = sl4R0 a' b' c' d' := congrArg Subtype.val h
      have hi := (isLongRootSL2_sl4R1 a b c d).involution_unique h2
        (hR ▸ isLongRootSL2_sl4R0 a' b' c' d')
      have hm := congrArg (fun A : SL(4, 𝔽₃) => (A : Matrix (Fin 4) (Fin 4) 𝔽₃)) hi
      simp only [coe_sl4Inv0, coe_sl4Inv1] at hm
      have h00 : (1 : 𝔽₃) = -1 := congrFun (congrFun hm 0) 0
      have : (2 : 𝔽₃) = 0 := by linear_combination h00
      exact h2 this
    · have hR : sl4R1 a b c d = sl4R1 a' b' c' d' := congrArg Subtype.val h
      have hi' : IsLongRootSL2 (show 2 ≤ 4 by norm_num) (sl4R1 a b c d)
          (sl4Inv1 a' b' c' d') := by
        rw [hR]
        exact isLongRootSL2_sl4R1 a' b' c' d'
      have hi := (isLongRootSL2_sl4R1 a b c d).involution_unique h2 hi'
      have hm := congrArg (fun A : SL(4, 𝔽₃) => (A : Matrix (Fin 4) (Fin 4) 𝔽₃)) hi
      simp only [coe_sl4Inv1] at hm
      have h02 : -(2 * a) = -(2 * a') := congrFun (congrFun hm 0) 2
      have h03 : -(2 * b) = -(2 * b') := congrFun (congrFun hm 0) 3
      have h12 : -(2 * c) = -(2 * c') := congrFun (congrFun hm 1) 2
      have h13 : -(2 * d) = -(2 * d') := congrFun (congrFun hm 1) 3
      rw [mul_left_cancel₀ h2 (neg_inj.mp h02), mul_left_cancel₀ h2 (neg_inj.mp h03),
        mul_left_cancel₀ h2 (neg_inj.mp h12), mul_left_cancel₀ h2 (neg_inj.mp h13)]
  have hfin : Finite {R : Subgroup SL(4, 𝔽₃) //
      R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D} := inferInstance
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, Nat.card_prod, Q3W.card_gf3] at hc
  omega

end CFSG.ClassicalInvolution.Q3.Q3TIY
