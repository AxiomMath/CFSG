module

public import CFSG.GroupTheory.GL52.InvolutionsConj
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

theorem inv_u0_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {invU0}) :
    (g : M5) * invU0M = invU0M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [invU0] using this

theorem inv_u0_shape {g : G52} (hg : g ∈ Subgroup.centralizer {invU0}) :
    (g : M5) 2 0 = 0 ∧ (g : M5) 3 0 = 0 ∧ (g : M5) 4 0 = 0 ∧ (g : M5) 2 1 = 0 ∧
      (g : M5) 3 1 = 0 ∧ (g : M5) 4 1 = 0 ∧ (g : M5) 3 2 = 0 ∧ (g : M5) 4 2 = 0 ∧
      (g : M5) 3 3 = (g : M5) 0 0 ∧ (g : M5) 3 4 = (g : M5) 0 1 ∧
      (g : M5) 4 3 = (g : M5) 1 0 ∧ (g : M5) 4 4 = (g : M5) 1 1 := by
  have hc := inv_u0_matrix_commute hg
  have e : ∀ i j, ((g : M5) * invU0M) i j = (invU0M * (g : M5)) i j := fun i j => by rw [hc]
  have e23 := e 2 3
  have e33 := e 3 3
  have e43 := e 4 3
  have e24 := e 2 4
  have e34 := e 3 4
  have e44 := e 4 4
  have e02 := e 0 2
  have e12 := e 1 2
  have e03 := e 0 3
  have e04 := e 0 4
  have e13 := e 1 3
  have e14 := e 1 4
  simp [invU0M, Matrix.mul_apply, Fin.sum_univ_five] at e23 e33 e43 e24 e34 e44 e02 e12
  simp [invU0M, Matrix.mul_apply, Fin.sum_univ_five] at e03 e04 e13 e14
  refine ⟨e23, e33, e43, e24, e34, e44, e02, e12, ?_, ?_, ?_, ?_⟩
  · linear_combination e03.symm
  · linear_combination e04.symm
  · linear_combination e13.symm
  · linear_combination e14.symm

@[expose] def invBlk (g : M5) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun a b => g a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc

theorem invBlk_mul (g : M5) {h : M5} (h20 : h 2 0 = 0) (h30 : h 3 0 = 0) (h40 : h 4 0 = 0)
    (h21 : h 2 1 = 0) (h31 : h 3 1 = 0) (h41 : h 4 1 = 0) :
    invBlk (g * h) = invBlk g * invBlk h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [invBlk, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two, h20, h30, h40, h21, h31,
      h41]

theorem invBlk_one : invBlk 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem invBlk_mul_of_mem (g : M5) {h : G52} (hh : h ∈ Subgroup.centralizer {invU0}) :
    invBlk (g * (h : M5)) = invBlk g * invBlk (h : M5) := by
  obtain ⟨h20, h30, h40, h21, h31, h41, -⟩ := inv_u0_shape hh
  exact invBlk_mul g h20 h30 h40 h21 h31 h41

@[expose] def invRho : Subgroup.centralizer {invU0} →* GL (Fin 2) (ZMod 2) where
  toFun g := ⟨invBlk (g : G52), invBlk ((g⁻¹ : Subgroup.centralizer {invU0}) : G52), by
    rw [← invBlk_mul_of_mem _ (g⁻¹).2, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel,
      Units.val_one, invBlk_one], by
    rw [← invBlk_mul_of_mem _ g.2, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel,
      Units.val_one, invBlk_one]⟩
  map_one' := Units.ext (by simp [invBlk_one])
  map_mul' g h := Units.ext (by
    change invBlk ((g : G52) * (h : G52) : G52) = invBlk (g : G52) * invBlk (h : G52)
    rw [Units.val_mul, invBlk_mul_of_mem _ h.2])

@[expose] def invDM (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : M5 :=
  !![M 0 0, M 0 1, 0, 0, 0; M 1 0, M 1 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, M 0 0, M 0 1;
    0, 0, 0, M 1 0, M 1 1]

theorem invDM_mul (M M' : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    invDM M * invDM M' = invDM (M * M') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invDM, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two]

theorem invDM_one : invDM 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem invDM_commute (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    invDM M * invU0M = invU0M * invDM M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invDM, invU0M, Matrix.mul_apply, Fin.sum_univ_five]

theorem invRho_surjective : Function.Surjective invRho := by
  intro M
  have hM : invDM (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
      invDM ((M⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    rw [invDM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, invDM_one]
  refine ⟨⟨mk5 _ _ hM, ?_⟩, Units.ext ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_mk5, invU0]
    exact invDM_commute _
  · change invBlk (invDM (M : Matrix (Fin 2) (Fin 2) (ZMod 2))) = (M : Matrix _ _ _)
    ext a b
    fin_cases a <;> fin_cases b <;> rfl

@[expose] def invQM (c : Fin 8 → ZMod 2) : M5 :=
  !![1, 0, c 0, c 1, c 2; 0, 1, c 3, c 4, c 5; 0, 0, 1, c 6, c 7; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def invQInv (c : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  ![c 0, c 1 + c 0 * c 6, c 2 + c 0 * c 7, c 3, c 4 + c 3 * c 6, c 5 + c 3 * c 7, c 6, c 7]

set_option maxRecDepth 100000 in
theorem invQM_facts : ∀ c : Fin 8 → ZMod 2, invQM c * invQM (invQInv c) = 1 := by
  decide +kernel

theorem invQM_commute (c : Fin 8 → ZMod 2) : invQM c * invU0M = invU0M * invQM c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invQM, invU0M, Matrix.mul_apply, Fin.sum_univ_five, add_comm]

theorem invQM_blk (c : Fin 8 → ZMod 2) : invBlk (invQM c) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem invQM_injective : Function.Injective invQM := by
  intro c c' h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 0) 4
  · exact congrFun (congrFun h 1) 2
  · exact congrFun (congrFun h 1) 3
  · exact congrFun (congrFun h 1) 4
  · exact congrFun (congrFun h 2) 3
  · exact congrFun (congrFun h 2) 4

@[expose] def invQElt (c : Fin 8 → ZMod 2) : invRho.ker :=
  ⟨⟨mk5 (invQM c) (invQM (invQInv c)) (invQM_facts c), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_mk5, invU0]
    exact invQM_commute c⟩, by
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    change invBlk (invQM c) = 1
    exact invQM_blk c⟩

theorem invQElt_surjective : Function.Surjective invQElt := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hblk : invBlk (g : M5) = 1 := by
    have := congrArg (fun x : GL (Fin 2) (ZMod 2) => (x : Matrix (Fin 2) (Fin 2) (ZMod 2)))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b00 : (g : M5) 0 0 = 1 := congrFun (congrFun hblk 0) 0
  have b01 : (g : M5) 0 1 = 0 := congrFun (congrFun hblk 0) 1
  have b10 : (g : M5) 1 0 = 0 := congrFun (congrFun hblk 1) 0
  have b11 : (g : M5) 1 1 = 1 := congrFun (congrFun hblk 1) 1
  obtain ⟨s20, s30, s40, s21, s31, s41, s32, s42, s33, s34, s43, s44⟩ := inv_u0_shape hg
  have s22 : (g : M5) 2 2 = 1 := by
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    refine key _ fun h0 => ?_
    have hz : (g : M5) *ᵥ (Pi.single 2 1 + (g : M5) 0 2 • Pi.single 0 1 +
        (g : M5) 1 2 • Pi.single 1 1) = 0 := by
      ext i
      fin_cases i <;>
        simp [mulVec, dotProduct, Fin.sum_univ_five, b00, b01, b10, b11, s20, s30, s40, s21,
          s31, s41, s32, s42, h0, CharTwo.add_self_eq_zero]
    have h1 := eq_zero_of_mulVec_eq_zero g hz
    have key2 : ∀ a b : ZMod 2,
        Pi.single 2 1 + a • Pi.single 0 1 + b • Pi.single 1 1 ≠ (0 : V5) := by decide
    exact key2 _ _ h1
  refine ⟨![(g : M5) 0 2, (g : M5) 0 3, (g : M5) 0 4, (g : M5) 1 2, (g : M5) 1 3, (g : M5) 1 4,
    (g : M5) 2 3, (g : M5) 2 4], ?_⟩
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change invQM _ = (g : M5)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invQM, b00, b01, b10, b11, s20, s30, s40, s21, s31, s41, s32, s42, s33, s34, s43, s44,
      s22]

theorem invQElt_injective : Function.Injective invQElt := by
  intro c c' h
  apply invQM_injective
  have := congrArg (fun x : invRho.ker => (((x : Subgroup.centralizer {invU0}) : G52) : M5)) h
  exact this

theorem inv_card_ker_rho : Nat.card invRho.ker = 256 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨invQElt_injective, invQElt_surjective⟩),
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem inv_card_centralizer_u0 : Nat.card (Subgroup.centralizer {invU0}) = 2 ^ 9 * 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup invRho.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ invRho_surjective).toEquiv,
    inv_card_ker_rho, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at h
  rw [h]
  norm_num

end CFSG.GroupTheory.GL52
