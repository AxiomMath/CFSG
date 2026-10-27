module

public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.ClassicalInvolution.WeakCT.SpAut

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open Matrix
open scoped MatrixGroups

section FieldTwoAux

variable {K : Type} [Field K]

theorem eq_zero_or_one_of_card_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((huniq c hc).trans (huniq 1 one_ne_zero).symm)

theorem one_add_one_eq_zero (hK : Nat.card K = 2) : (1 : K) + 1 = 0 := by
  rcases eq_zero_or_one_of_card_two hK ((1 : K) + 1) with h | h
  · exact h
  · exact absurd (add_right_cancel (h.trans (zero_add 1).symm)) one_ne_zero

private theorem neg_eq_self_of_card_two (hK : Nat.card K = 2) (x : K) : -x = x := by
  have h2 := one_add_one_eq_zero hK
  have hx : x + x = 0 := by
    have h : x * (1 + 1) = 0 := by rw [h2, mul_zero]
    simpa [mul_add] using h
  exact neg_eq_of_add_eq_zero_right hx

theorem tv_zero_eq_one {n : ℕ} (i j : Fin n) :
    (tv i j (0 : K) : SL(n, K)) = 1 := by
  by_cases h : i = j
  · simp [tv, h]
  · rw [tv_of_ne h, Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem tv01_mul_self (hK : Nat.card K = 2) :
    (tv 0 1 (1 : K) : SL(2, K)) * tv 0 1 1 = 1 := by
  rw [tv_of_ne (by decide : (0 : Fin 2) ≠ 1),
    ← Matrix.SpecialLinearGroup.transvection_add, one_add_one_eq_zero hK,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem tv10_mul_self (hK : Nat.card K = 2) :
    (tv 1 0 (1 : K) : SL(2, K)) * tv 1 0 1 = 1 := by
  rw [tv_of_ne (by decide : (1 : Fin 2) ≠ 0),
    ← Matrix.SpecialLinearGroup.transvection_add, one_add_one_eq_zero hK,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem tv01_ne_one : (tv 0 1 (1 : K) : SL(2, K)) ≠ 1 := by
  intro h
  have h' : ((tv 0 1 (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have h2 := congrFun (congrFun (congrArg (fun g : SL(2, K) =>
      ((g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) h) 0) 1
    simpa using h2
  rw [tv01_eq_sl2Upper, coe_sl2Upper] at h'
  simpa using h'

theorem tv10_ne_one : (tv 1 0 (1 : K) : SL(2, K)) ≠ 1 := by
  intro h
  have h' : ((tv 1 0 (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h2 := congrFun (congrFun (congrArg (fun g : SL(2, K) =>
      ((g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) h) 1) 0
    simpa using h2
  rw [tv10_eq_sl2Lower, coe_sl2Lower] at h'
  simpa using h'

theorem tv01_ne_tv10 : (tv 0 1 (1 : K) : SL(2, K)) ≠ tv 1 0 1 := by
  intro h
  have h' : ((tv 0 1 (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((tv 1 0 (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 :=
    congrFun (congrFun (congrArg (fun g : SL(2, K) =>
      ((g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) h) 1) 0
  rw [tv01_eq_sl2Upper, tv10_eq_sl2Lower, coe_sl2Upper, coe_sl2Lower] at h'
  exact zero_ne_one h'

theorem hom_ext_sl2_two (hK : Nat.card K = 2) {X : Type*} [Group X]
    {f g : SL(2, K) →* X} (hu : f (tv 0 1 (1 : K)) = g (tv 0 1 1))
    (hv : f (tv 1 0 (1 : K)) = g (tv 1 0 1)) : f = g := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
    · rw [tv_zero_eq_one, map_one, map_one]
    · exact hu
  · rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
    · rw [tv_zero_eq_one, map_one, map_one]
    · exact hv

theorem invTransposeSL_blk (s : Fin 2) (A : SL(2, K)) :
    invTransposeSL 3 (blk K s A) = blk K s (invTransposeSL 2 A) := by
  fin_cases s
  · exact invTransposeSL_blockSL (by omega) A
  · exact invTransposeSL_blockSL (by omega) A

theorem invTransposeSL_tv01_one (hK : Nat.card K = 2) :
    invTransposeSL 2 (tv 0 1 (1 : K)) = tv 1 0 1 := by
  rw [invTransposeSL_tv01, neg_eq_self_of_card_two hK]

theorem invTransposeSL_tv10_one (hK : Nat.card K = 2) :
    invTransposeSL 2 (tv 1 0 (1 : K)) = tv 0 1 1 := by
  rw [invTransposeSL_tv10, neg_eq_self_of_card_two hK]

theorem center_SL_three_eq_bot (hK : Nat.card K = 2) : Subgroup.center SL(3, K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨ω, hω0, -, -, hω1⟩ := exists_eq_of_mem_center hg
  exact hω1 (by
    rcases eq_zero_or_one_of_card_two hK ω with h | h
    · exact absurd h hω0
    · exact h)

private theorem cm_blk_zero_tv01 :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (tv 0 1 (1 : K))) =
      !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  rw [show blk K 0 (tv 0 1 (1 : K)) = tv 0 1 1 from blk_zero_tv01 1]
  exact cm_tv01 1

private theorem cm_blk_one_tv01 :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (tv 0 1 (1 : K))) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] := by
  rw [show blk K 1 (tv 0 1 (1 : K)) = tv 1 2 1 from blk_one_tv01 1]
  exact cm_tv12 1

private theorem cm_blk_zero_tv10 :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (tv 1 0 (1 : K))) =
      !![1, 0, 0; 1, 1, 0; 0, 0, 1] := by
  rw [show blk K 0 (tv 1 0 (1 : K)) = tv 1 0 1 from blk_zero_tv10 1]
  exact cm_tv10 1

private theorem cm_blk_one_tv10 :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (tv 1 0 (1 : K))) =
      !![1, 0, 0; 0, 1, 0; 0, 1, 1] := by
  rw [show blk K 1 (tv 1 0 (1 : K)) = tv 2 1 1 from blk_one_tv10 1]
  exact cm_tv21 1

private theorem cm_blk_zero (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 A) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  rw [show blk K 0 A = blockSL K 3 2 0 (by omega) A from rfl]
  exact coe_blockSL_three_zero A

private theorem cm_blk_one (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 A) =
      !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1] := by
  rw [show blk K 1 A = blockSL K 3 2 1 (by omega) A from rfl]
  exact coe_blockSL_three_one A

private theorem blk_zero_tv01_comm_blk_one_tv10 :
    blk K 0 (tv 0 1 (1 : K)) * blk K 1 (tv 1 0 (1 : K)) =
      blk K 1 (tv 1 0 (1 : K)) * blk K 0 (tv 0 1 (1 : K)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul]
  rw [cm_blk_zero_tv01, cm_blk_one_tv10, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem blk_one_tv01_comm_blk_zero_tv10 :
    blk K 1 (tv 0 1 (1 : K)) * blk K 0 (tv 1 0 (1 : K)) =
      blk K 0 (tv 1 0 (1 : K)) * blk K 1 (tv 0 1 (1 : K)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul]
  rw [cm_blk_one_tv01, cm_blk_zero_tv10, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem blk_zero_tv10_comm_blk_one_tv01 :
    blk K 0 (tv 1 0 (1 : K)) * blk K 1 (tv 0 1 (1 : K)) =
      blk K 1 (tv 0 1 (1 : K)) * blk K 0 (tv 1 0 (1 : K)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul]
  rw [cm_blk_zero_tv10, cm_blk_one_tv01, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem blk_one_tv10_comm_blk_zero_tv01 :
    blk K 1 (tv 1 0 (1 : K)) * blk K 0 (tv 0 1 (1 : K)) =
      blk K 0 (tv 0 1 (1 : K)) * blk K 1 (tv 1 0 (1 : K)) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul]
  rw [cm_blk_one_tv10, cm_blk_zero_tv01, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_one_of_mem_Bs_rev_comm (s : Fin 2) {c : SL(3, K)}
    (hc : c ∈ Bs K s.rev) (hcomm : ∀ b ∈ Bs K s, c * b = b * c) : c = 1 := by
  fin_cases s
  · obtain ⟨A, rfl⟩ : ∃ A : SL(2, K), blk K 1 A = c := hc
    have hu := hcomm (blk K 0 (tv 0 1 (1 : K))) (blk_mem_Bs 0 (tv 0 1 1))
    have hv := hcomm (blk K 0 (tv 1 0 (1 : K))) (blk_mem_Bs 0 (tv 1 0 1))
    have hu' : Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 A) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (tv 0 1 (1 : K))) =
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (tv 0 1 (1 : K))) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 A) := by
      have h := congrArg Matrix.SpecialLinearGroup.coeMonoidHom hu
      simpa only [map_mul] using h
    have hv' : Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 A) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (tv 1 0 (1 : K))) =
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (tv 1 0 (1 : K))) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 A) := by
      have h := congrArg Matrix.SpecialLinearGroup.coeMonoidHom hv
      simpa only [map_mul] using h
    rw [cm_blk_one A, cm_blk_zero_tv01, Matrix.mul_fin_three] at hu'
    rw [cm_blk_one A, cm_blk_zero_tv10, Matrix.mul_fin_three] at hv'
    have hA00 : A 0 0 = 1 := by
      have h := congrFun (congrFun hu' 0) 1
      simpa using h.symm
    have hA01 : A 0 1 = 0 := by
      have h := congrFun (congrFun hu' 0) 2
      simpa using h.symm
    have hA10 : A 1 0 = 0 := by
      have h := congrFun (congrFun hv' 2) 0
      simpa using h
    have hA11 : A 1 1 = 1 := by
      have hdet := A.2
      rw [Matrix.det_fin_two, hA00, hA10] at hdet
      simpa using hdet
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    rw [cm_blk_one A, hA00, hA01, hA10, hA11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · obtain ⟨A, rfl⟩ : ∃ A : SL(2, K), blk K 0 A = c := hc
    have hu := hcomm (blk K 1 (tv 0 1 (1 : K))) (blk_mem_Bs 1 (tv 0 1 1))
    have hv := hcomm (blk K 1 (tv 1 0 (1 : K))) (blk_mem_Bs 1 (tv 1 0 1))
    have hu' : Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 A) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (tv 0 1 (1 : K))) =
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (tv 0 1 (1 : K))) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 A) := by
      have h := congrArg Matrix.SpecialLinearGroup.coeMonoidHom hu
      simpa only [map_mul] using h
    have hv' : Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 A) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (tv 1 0 (1 : K))) =
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (tv 1 0 (1 : K))) *
        Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 A) := by
      have h := congrArg Matrix.SpecialLinearGroup.coeMonoidHom hv
      simpa only [map_mul] using h
    rw [cm_blk_zero A, cm_blk_one_tv01, Matrix.mul_fin_three] at hu'
    rw [cm_blk_zero A, cm_blk_one_tv10, Matrix.mul_fin_three] at hv'
    have hA01 : A 0 1 = 0 := by
      have h := congrFun (congrFun hu' 0) 2
      simpa using h
    have hA11 : A 1 1 = 1 := by
      have h := congrFun (congrFun hu' 1) 2
      simpa using h
    have hA10 : A 1 0 = 0 := by
      have h := congrFun (congrFun hv' 2) 0
      simpa using h.symm
    have hA00 : A 0 0 = 1 := by
      have hdet := A.2
      rw [Matrix.det_fin_two, hA01, hA10, hA11] at hdet
      simpa using hdet
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    rw [cm_blk_zero A, hA00, hA01, hA10, hA11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem blk_tv01_comm_blk_rev_tv10 (t : Fin 2) :
    blk K t (tv 0 1 (1 : K)) * blk K t.rev (tv 1 0 (1 : K)) =
      blk K t.rev (tv 1 0 (1 : K)) * blk K t (tv 0 1 (1 : K)) := by
  fin_cases t
  · exact blk_zero_tv01_comm_blk_one_tv10
  · exact blk_one_tv01_comm_blk_zero_tv10

theorem blk_tv10_comm_blk_rev_tv01 (t : Fin 2) :
    blk K t (tv 1 0 (1 : K)) * blk K t.rev (tv 0 1 (1 : K)) =
      blk K t.rev (tv 0 1 (1 : K)) * blk K t (tv 1 0 (1 : K)) := by
  fin_cases t
  · exact blk_zero_tv10_comm_blk_one_tv01
  · exact blk_one_tv10_comm_blk_zero_tv01

theorem blk_rev_tv10_ne_one (t : Fin 2) : blk K t.rev (tv 1 0 (1 : K)) ≠ 1 := by
  have ht : t.rev = 0 ∨ t.rev = 1 := by
    fin_cases t <;> decide
  intro h
  rcases ht with ht | ht
  · rw [ht] at h
    exact tv10_ne_one (blk_injective (K := K) 0 (by rw [h, map_one]))
  · rw [ht] at h
    exact tv10_ne_one (blk_injective (K := K) 1 (by rw [h, map_one]))

theorem blk_rev_tv01_ne_one (t : Fin 2) : blk K t.rev (tv 0 1 (1 : K)) ≠ 1 := by
  have ht : t.rev = 0 ∨ t.rev = 1 := by
    fin_cases t <;> decide
  intro h
  rcases ht with ht | ht
  · rw [ht] at h
    exact tv01_ne_one (blk_injective (K := K) 0 (by rw [h, map_one]))
  · rw [ht] at h
    exact tv01_ne_one (blk_injective (K := K) 1 (by rw [h, map_one]))

end FieldTwoAux

end CFSG.ClassicalInvolution.WeakCT
