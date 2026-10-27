module

public import CFSG.ClassicalInvolution.WeakCT.FieldTwoAux
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalGroups.SpecialLinear
open Matrix
open scoped MatrixGroups commutatorElement

section FieldTwo

variable {K : Type} [Field K] [Finite K]

@[expose] def weylTwo (K : Type) [Field K] : SL(2, K) :=
  tv 0 1 (1 : K) * tv 1 0 (1 : K) * tv 0 1 (1 : K)

private theorem cm2_tv01 (c : K) :
    Matrix.SpecialLinearGroup.coeMonoidHom (tv 0 1 c : SL(2, K)) = !![1, c; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply, tv01_eq_sl2Upper, coe_sl2Upper]

private theorem cm2_tv10 (c : K) :
    Matrix.SpecialLinearGroup.coeMonoidHom (tv 1 0 c : SL(2, K)) = !![1, 0; c, 1] := by
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply, tv10_eq_sl2Lower, coe_sl2Lower]

private theorem cm_weylTwo (hK : Nat.card K = 2) :
    Matrix.SpecialLinearGroup.coeMonoidHom (weylTwo K) = !![0, 1; 1, 0] := by
  have h2 := one_add_one_eq_zero hK
  unfold weylTwo
  simp only [map_mul]
  rw [cm2_tv01, cm2_tv10]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h2]

private theorem weylTwo_coe (hK : Nat.card K = 2) :
    ((weylTwo K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  simpa only [Matrix.SpecialLinearGroup.coeMonoidHom_apply] using cm_weylTwo hK

theorem weylTwo_mul_self (hK : Nat.card K = 2) : weylTwo K * weylTwo K = 1 := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  rw [map_mul, map_one, cm_weylTwo hK, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_add_one_eq_zero hK]

theorem weylTwo_ne_one (hK : Nat.card K = 2) : weylTwo K ≠ 1 := by
  intro h
  have h' : ((weylTwo K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h2 := congrFun (congrFun (congrArg (fun g : SL(2, K) =>
      ((g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) h) 1) 1
    simpa using h2
  rw [weylTwo_coe hK] at h'
  exact zero_ne_one h'

theorem tv01_ne_weylTwo (hK : Nat.card K = 2) :
    (tv 0 1 (1 : K) : SL(2, K)) ≠ weylTwo K := by
  intro h
  have h' := congrFun (congrFun (congrArg Matrix.SpecialLinearGroup.coeMonoidHom h) 1) 1
  rw [cm2_tv01, cm_weylTwo hK] at h'
  exact one_ne_zero h'

theorem tv10_ne_weylTwo (hK : Nat.card K = 2) :
    (tv 1 0 (1 : K) : SL(2, K)) ≠ weylTwo K := by
  intro h
  have h' := congrFun (congrFun (congrArg Matrix.SpecialLinearGroup.coeMonoidHom h) 0) 1
  rw [cm2_tv10, cm_weylTwo hK] at h'
  exact zero_ne_one h'

theorem eq_one_or_tv_of_mul_self (hK : Nat.card K = 2) {A : SL(2, K)} (hA : A * A = 1) :
    A = 1 ∨ A = tv 0 1 (1 : K) ∨ A = tv 1 0 (1 : K) ∨ A = weylTwo K := by
  have h01 := eq_zero_or_one_of_card_two hK
  have h2 := one_add_one_eq_zero hK
  obtain ⟨a, b, c, d, hmat⟩ : ∃ a b c d : K, (A : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨A 0 0, A 0 1, A 1 0, A 1 1, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  have hA' : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, d] = 1 := by
    have h := congrArg (fun g : SL(2, K) => ((g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) hA
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hmat] at h
    exact h
  have h00 : a * a + b * c = 1 := by
    have h := congrFun (congrFun hA' 0) 0
    simpa [Matrix.mul_fin_two] using h
  have h11 : c * b + d * d = 1 := by
    have h := congrFun (congrFun hA' 1) 1
    simpa [Matrix.mul_fin_two] using h
  have haa : a * a = a := by rcases h01 a with rfl | rfl <;> simp
  have hdd : d * d = d := by rcases h01 d with rfl | rfl <;> simp
  have h00' : a + b * c = 1 := by simpa [haa] using h00
  have h11' : d + b * c = 1 := by
    have h := h11
    rw [hdd, mul_comm c b, add_comm] at h
    exact h
  have had : a = d := add_right_cancel (h00'.trans h11'.symm)
  rcases h01 a with ha | ha
  · rcases h01 b with hb | hb <;> rcases h01 c with hc | hc
    · exfalso
      rw [ha, hb, hc] at h00'
      simpa [h2] using h00'
    · exfalso
      rw [ha, hb, hc] at h00'
      simpa [h2] using h00'
    · exfalso
      rw [ha, hb, hc] at h00'
      simpa [h2] using h00'
    · right; right; right
      apply Subtype.ext
      rw [hmat, ← had, ha, hb, hc, weylTwo_coe hK] <;> ext i j <;> fin_cases i <;>
        fin_cases j <;> simp
  · rcases h01 b with hb | hb <;> rcases h01 c with hc | hc
    · left
      apply Subtype.ext
      rw [hmat, ← had, ha, hb, hc, Matrix.SpecialLinearGroup.coe_one] <;> ext i j <;>
        fin_cases i <;> fin_cases j <;> simp
    · right; right; left
      apply Subtype.ext
      rw [hmat, ← had, ha, hb, hc, tv10_eq_sl2Lower, coe_sl2Lower] <;> ext i j <;>
        fin_cases i <;> fin_cases j <;> simp
    · right; left
      apply Subtype.ext
      rw [hmat, ← had, ha, hb, hc, tv01_eq_sl2Upper, coe_sl2Upper] <;> ext i j <;>
        fin_cases i <;> fin_cases j <;> simp
    · exfalso
      rw [ha, hb, hc] at h00'
      simpa [h2] using h00'

theorem invTransposeSL_weylTwo (hK : Nat.card K = 2) :
    invTransposeSL 2 (weylTwo K) = weylTwo K := by
  have hinv : (weylTwo K)⁻¹ = weylTwo K := inv_eq_of_mul_eq_one_right (weylTwo_mul_self hK)
  apply Subtype.ext
  rw [coe_invTransposeSL, hinv, weylTwo_coe hK]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem cm_blk_zero_weylTwo (hK : Nat.card K = 2) :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 0 (weylTwo K)) =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  show ((blockSL K 3 2 0 (by omega) (weylTwo K) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylTwo_coe hK]

private theorem cm_blk_one_weylTwo (hK : Nat.card K = 2) :
    Matrix.SpecialLinearGroup.coeMonoidHom (blk K 1 (weylTwo K)) =
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  show ((blockSL K 3 2 1 (by omega) (weylTwo K) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
  rw [coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylTwo_coe hK]

private theorem cm_tv02 :
    Matrix.SpecialLinearGroup.coeMonoidHom (tv 0 2 (1 : K) : SL(3, K)) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply, tv_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem cm_tv20 :
    Matrix.SpecialLinearGroup.coeMonoidHom (tv 2 0 (1 : K) : SL(3, K)) =
      !![1, 0, 0; 0, 1, 0; 1, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply, tv_of_ne (by decide : (2 : Fin 3) ≠ 0),
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem blk_weylTwo_mul_self (hK : Nat.card K = 2) (s : Fin 2) :
    blk K s (weylTwo K) * blk K s (weylTwo K) = 1 := by
  rw [← map_mul, weylTwo_mul_self hK, map_one]

private theorem Bs_zero_le_closure_rev_weylTwo (hK : Nat.card K = 2) :
    Bs K 0 ≤ Subgroup.closure ((Bs K 1 : Set SL(3, K)) ∪ {blk K 0 (weylTwo K)}) := by
  let H := Subgroup.closure ((Bs K 1 : Set SL(3, K)) ∪ {blk K 0 (weylTwo K)})
  have hPH : blk K 0 (weylTwo K) ∈ H :=
    Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hrev : ∀ A : SL(2, K), blk K 1 A ∈ H := fun A =>
    Subgroup.subset_closure (Set.mem_union_left _ (blk_mem_Bs 1 A))
  have hPinv : (blk K 0 (weylTwo K))⁻¹ = blk K 0 (weylTwo K) :=
    inv_eq_of_mul_eq_one_right (blk_weylTwo_mul_self hK 0)
  have hconj1 : blk K 0 (weylTwo K) * blk K 1 (tv 0 1 (1 : K)) *
      (blk K 0 (weylTwo K))⁻¹ = tv 0 2 1 := by
    rw [hPinv, blk_one_tv01]
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    simp only [map_mul]
    rw [cm_blk_zero_weylTwo hK, cm_tv12, cm_tv02, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hconj2 : blk K 0 (weylTwo K) * blk K 1 (tv 1 0 (1 : K)) *
      (blk K 0 (weylTwo K))⁻¹ = tv 2 0 1 := by
    rw [hPinv, blk_one_tv10]
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    simp only [map_mul]
    rw [cm_blk_zero_weylTwo hK, cm_tv21, cm_tv20, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hm1 : blk K 0 (weylTwo K) * blk K 1 (tv 0 1 (1 : K)) *
      (blk K 0 (weylTwo K))⁻¹ ∈ H := H.mul_mem (H.mul_mem hPH (hrev _)) (H.inv_mem hPH)
  have hm2 : blk K 0 (weylTwo K) * blk K 1 (tv 1 0 (1 : K)) *
      (blk K 0 (weylTwo K))⁻¹ ∈ H := H.mul_mem (H.mul_mem hPH (hrev _)) (H.inv_mem hPH)
  have hcu : blk K 0 (tv 0 1 (1 : K)) ∈ H := by
    have h := steinberg_commutator (i := (0 : Fin 3)) (j := (2 : Fin 3)) (k := (1 : Fin 3))
      (by decide) (by decide) (by decide) (1 : K) (1 : K)
    rw [← tv_of_ne (by decide : (0 : Fin 3) ≠ 2), ← tv_of_ne (by decide : (2 : Fin 3) ≠ 1),
      ← tv_of_ne (by decide : (0 : Fin 3) ≠ 1), mul_one] at h
    rw [← hconj1, ← blk_one_tv10 (c := 1), ← blk_zero_tv01 (c := 1)] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hm1 (hrev _)) (H.inv_mem hm1)) (H.inv_mem (hrev _))
  have hcv : blk K 0 (tv 1 0 (1 : K)) ∈ H := by
    have h := steinberg_commutator (i := (1 : Fin 3)) (j := (2 : Fin 3)) (k := (0 : Fin 3))
      (by decide) (by decide) (by decide) (1 : K) (1 : K)
    rw [← tv_of_ne (by decide : (1 : Fin 3) ≠ 2), ← tv_of_ne (by decide : (2 : Fin 3) ≠ 0),
      ← tv_of_ne (by decide : (1 : Fin 3) ≠ 0), mul_one] at h
    rw [← blk_one_tv01 (c := 1), ← hconj2, ← blk_zero_tv10 (c := 1)] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hrev _) hm2) (H.inv_mem (hrev _))) (H.inv_mem hm2)
  have hu : ∀ c : K, blk K 0 (tv 0 1 c) ∈ H := by
    intro c
    rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
    · rw [tv_zero_eq_one, map_one]; exact one_mem H
    · exact hcu
  have hv : ∀ c : K, blk K 0 (tv 1 0 c) ∈ H := by
    intro c
    rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
    · rw [tv_zero_eq_one, map_one]; exact one_mem H
    · exact hcv
  exact range_le_of_tv (blk K 0) H hu hv

private theorem Bs_one_le_closure_rev_weylTwo (hK : Nat.card K = 2) :
    Bs K 1 ≤ Subgroup.closure ((Bs K 0 : Set SL(3, K)) ∪ {blk K 1 (weylTwo K)}) := by
  let H := Subgroup.closure ((Bs K 0 : Set SL(3, K)) ∪ {blk K 1 (weylTwo K)})
  have hPH : blk K 1 (weylTwo K) ∈ H :=
    Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hrev : ∀ A : SL(2, K), blk K 0 A ∈ H := fun A =>
    Subgroup.subset_closure (Set.mem_union_left _ (blk_mem_Bs 0 A))
  have hPinv : (blk K 1 (weylTwo K))⁻¹ = blk K 1 (weylTwo K) :=
    inv_eq_of_mul_eq_one_right (blk_weylTwo_mul_self hK 1)
  have hconj1 : blk K 1 (weylTwo K) * blk K 0 (tv 0 1 (1 : K)) *
      (blk K 1 (weylTwo K))⁻¹ = tv 0 2 1 := by
    rw [hPinv, blk_zero_tv01]
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    simp only [map_mul]
    rw [cm_blk_one_weylTwo hK, cm_tv01, cm_tv02, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hconj2 : blk K 1 (weylTwo K) * blk K 0 (tv 1 0 (1 : K)) *
      (blk K 1 (weylTwo K))⁻¹ = tv 2 0 1 := by
    rw [hPinv, blk_zero_tv10]
    apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
    simp only [map_mul]
    rw [cm_blk_one_weylTwo hK, cm_tv10, cm_tv20, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hm1 : blk K 1 (weylTwo K) * blk K 0 (tv 0 1 (1 : K)) *
      (blk K 1 (weylTwo K))⁻¹ ∈ H := H.mul_mem (H.mul_mem hPH (hrev _)) (H.inv_mem hPH)
  have hm2 : blk K 1 (weylTwo K) * blk K 0 (tv 1 0 (1 : K)) *
      (blk K 1 (weylTwo K))⁻¹ ∈ H := H.mul_mem (H.mul_mem hPH (hrev _)) (H.inv_mem hPH)
  have hcu : blk K 1 (tv 0 1 (1 : K)) ∈ H := by
    have h := steinberg_commutator (i := (1 : Fin 3)) (j := (0 : Fin 3)) (k := (2 : Fin 3))
      (by decide) (by decide) (by decide) (1 : K) (1 : K)
    rw [← tv_of_ne (by decide : (1 : Fin 3) ≠ 0), ← tv_of_ne (by decide : (0 : Fin 3) ≠ 2),
      ← tv_of_ne (by decide : (1 : Fin 3) ≠ 2), mul_one] at h
    rw [← blk_zero_tv10 (c := 1), ← hconj1, ← blk_one_tv01 (c := 1)] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hrev _) hm1) (H.inv_mem (hrev _))) (H.inv_mem hm1)
  have hcv : blk K 1 (tv 1 0 (1 : K)) ∈ H := by
    have h := steinberg_commutator (i := (2 : Fin 3)) (j := (0 : Fin 3)) (k := (1 : Fin 3))
      (by decide) (by decide) (by decide) (1 : K) (1 : K)
    rw [← tv_of_ne (by decide : (2 : Fin 3) ≠ 0), ← tv_of_ne (by decide : (0 : Fin 3) ≠ 1),
      ← tv_of_ne (by decide : (2 : Fin 3) ≠ 1), mul_one] at h
    rw [← hconj2, ← blk_zero_tv01 (c := 1), ← blk_one_tv10 (c := 1)] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hm2 (hrev _)) (H.inv_mem hm2)) (H.inv_mem (hrev _))
  have hu : ∀ c : K, blk K 1 (tv 0 1 c) ∈ H := by
    intro c
    rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
    · rw [tv_zero_eq_one, map_one]; exact one_mem H
    · exact hcu
  have hv : ∀ c : K, blk K 1 (tv 1 0 c) ∈ H := by
    intro c
    rcases eq_zero_or_one_of_card_two hK c with rfl | rfl
    · rw [tv_zero_eq_one, map_one]; exact one_mem H
    · exact hcv
  exact range_le_of_tv (blk K 1) H hu hv

theorem Bs_le_closure_rev_weylTwo (hK : Nat.card K = 2) (s : Fin 2) :
    Bs K s ≤ Subgroup.closure ((Bs K s.rev : Set SL(3, K)) ∪ {blk K s (weylTwo K)}) := by
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s <;> simp
  rcases hs with rfl | rfl
  · exact Bs_zero_le_closure_rev_weylTwo hK
  · exact Bs_one_le_closure_rev_weylTwo hK

end FieldTwo

end CFSG.ClassicalInvolution.WeakCT
