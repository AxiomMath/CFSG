module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockIdx blockMat_apply blockMat_apply_blockIdx blockMat_comm)
open scoped MatrixGroups

theorem pb_blockSL2_zero (A : SL(2, F4)) :
    (blockSL2 F4 3 0 A : Matrix (Fin 4) (Fin 4) F4) =
      !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  rw [blockSL2_three_apply, blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem pb_blockSL2_two (A : SL(2, F4)) :
    (blockSL2 F4 3 2 A : Matrix (Fin 4) (Fin 4) F4) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] := by
  ext i j
  rw [blockSL2_three_apply, blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem blockSL2_comm (A B : SL(2, F4)) :
    blockSL2 F4 3 0 A * blockSL2 F4 3 2 B = blockSL2 F4 3 2 B * blockSL2 F4 3 0 A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact blockMat_comm (Or.inl (by norm_num)) (A : Matrix (Fin 2) (Fin 2) F4)
    (B : Matrix (Fin 2) (Fin 2) F4)

theorem blockSL2_injective (k : Fin 3) : Function.Injective (blockSL2 F4 3 k) := by
  intro A B h
  have hk : (k : ℕ) + 2 ≤ 4 := by have := k.isLt; omega
  apply Subtype.ext
  ext x y
  have e1 := (blockSL2_three_apply F4 k A (blockIdx k hk x) (blockIdx k hk y)).trans
    (blockMat_apply_blockIdx hk (A : Matrix (Fin 2) (Fin 2) F4) x y)
  have e2 := (blockSL2_three_apply F4 k B (blockIdx k hk x) (blockIdx k hk y)).trans
    (blockMat_apply_blockIdx hk (B : Matrix (Fin 2) (Fin 2) F4) x y)
  rw [h] at e1
  exact e1.symm.trans e2

theorem blockSL2_conj_YK₀ (A : SL(2, F4)) {y : SL(4, F4)} (hy : y ∈ YK) :
    blockSL2 F4 3 0 A * y * (blockSL2 F4 3 0 A)⁻¹ ∈ YK := by
  obtain ⟨a₂, a₄, a₅, a₈, rfl⟩ := hy
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.2
    rwa [Matrix.det_fin_two] at h
  have key : blockSL2 F4 3 0 A * pSL 0 a₂ 0 a₄ a₅ a₈ =
      pSL 0 (a₂ * A 0 0 - a₄ * A 0 1) 0 (a₄ * A 1 1 - a₂ * A 1 0)
        (a₅ * A 0 0 - a₈ * A 0 1) (a₈ * A 1 1 - a₅ * A 1 0) * blockSL2 F4 3 0 A := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_pSL,
      pb_blockSL2_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first
      | ring1
      | linear_combination a₄ * hdet
      | linear_combination (-a₄) * hdet
      | linear_combination a₂ * hdet
      | linear_combination (-a₂) * hdet
      | linear_combination a₈ * hdet
      | linear_combination (-a₈) * hdet
      | linear_combination a₅ * hdet
      | linear_combination (-a₅) * hdet
  rw [key, mul_inv_cancel_right]
  exact ⟨_, _, _, _, rfl⟩

theorem blockSL2_conj_YK₂ (A : SL(2, F4)) {y : SL(4, F4)} (hy : y ∈ YK) :
    blockSL2 F4 3 2 A * y * (blockSL2 F4 3 2 A)⁻¹ ∈ YK := by
  obtain ⟨a₂, a₄, a₅, a₈, rfl⟩ := hy
  have key : blockSL2 F4 3 2 A * pSL 0 a₂ 0 a₄ a₅ a₈ =
      pSL 0 (A 0 0 * a₂ + A 0 1 * a₅) 0 (A 0 0 * a₄ + A 0 1 * a₈)
        (A 1 0 * a₂ + A 1 1 * a₅) (A 1 0 * a₄ + A 1 1 * a₈) * blockSL2 F4 3 2 A := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_pSL,
      pb_blockSL2_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring1
  rw [key, mul_inv_cancel_right]
  exact ⟨_, _, _, _, rfl⟩

theorem rootSL_le_range₀ : rootSL F4 1 0 ≤ (blockSL2 F4 3 0).range := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨h, c, rfl⟩
  exact ⟨_, blockSL2_transvection_one_zero F4 0 one_ne_zero c⟩

theorem rootSL_le_range₂ : rootSL F4 3 2 ≤ (blockSL2 F4 3 2).range := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨h, c, rfl⟩
  exact ⟨_, blockSL2_transvection_one_zero F4 2 one_ne_zero c⟩

theorem pb_sl2_factor (A : SL(2, F4)) (hA : A 0 1 ≠ 0) (u : F4) :
    (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) u : SL(2, F4)) =
      SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (A 1 1 * (A 0 1)⁻¹) *
        (A * SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0)
          (u * ((A 0 1)⁻¹ * (A 0 1)⁻¹)) * A⁻¹) *
        SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (A 1 1 * (A 0 1)⁻¹) := by
  obtain ⟨a, b, e, d, hM⟩ : ∃ a b e d : F4, (A : Matrix (Fin 2) (Fin 2) F4) = !![a, b; e, d] :=
    ⟨A 0 0, A 0 1, A 1 0, A 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have hdet : a * d - b * e = 1 := by
    have h := A.2
    rw [Matrix.det_fin_two, hM] at h
    simpa using h
  have hb : b ≠ 0 := by
    have h : (A : Matrix (Fin 2) (Fin 2) F4) 0 1 ≠ 0 := hA
    rw [hM] at h
    simpa using h
  clear hA
  apply Subtype.ext
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_two, one_apply, single_apply, hM]
  fin_cases i <;> fin_cases j <;> simp
  all_goals clear hM
  all_goals (revert hdet hb; revert a b e d u; decide +kernel)

theorem pb_rootSL_castSucc_le_sup (k : Fin 3) {A : SL(2, F4)} (hA : A 0 1 ≠ 0) :
    rootSL F4 k.castSucc k.succ ≤
      rootSL F4 k.succ k.castSucc ⊔
        (rootSL F4 k.succ k.castSucc).map (MulAut.conj (blockSL2 F4 3 k A)).toMonoidHom := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨h, c, rfl⟩
  have hlow : ∀ s : F4, blockSL2 F4 3 k (SpecialLinearGroup.transvection
      (one_ne_zero : (1 : Fin 2) ≠ 0) s) ∈ rootSL F4 k.succ k.castSucc := fun s => by
    rw [blockSL2_transvection_one_zero F4 k one_ne_zero s]
    exact subset_closure ⟨_, s, rfl⟩
  have e : (SpecialLinearGroup.transvection h c : SL(4, F4)) =
      blockSL2 F4 3 k (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) :=
    (blockSL2_transvection_zero_one F4 k zero_ne_one c).symm
  rw [e, pb_sl2_factor A hA c]
  simp only [map_mul, map_inv]
  exact mul_mem (mul_mem (mem_sup_left (hlow _))
      (mem_sup_right (Subgroup.mem_map.mpr ⟨_, hlow (c * ((A 0 1)⁻¹ * (A 0 1)⁻¹)), rfl⟩)))
    (mem_sup_left (hlow _))

theorem range₀_le_sup {A : SL(2, F4)} (hA : A 0 1 ≠ 0) :
    (blockSL2 F4 3 0).range ≤
      rootSL F4 1 0 ⊔ (rootSL F4 1 0).map (MulAut.conj (blockSL2 F4 3 0 A)).toMonoidHom := by
  have hsup : rootSL F4 1 0 ⊔ rootSL F4 0 1 = (blockSL2 F4 3 0).range :=
    rootSL_sup_rootSL_eq_range F4 0
  rw [← hsup]
  exact sup_le le_sup_left (pb_rootSL_castSucc_le_sup 0 hA)

@[expose] def pbEta : SL(2, F4) :=
  ⟨!![F4.ω, 0; 0, F4.ω ^ 2], by rw [Matrix.det_fin_two_of]; decide⟩

theorem pbEta_ne_one : pbEta ≠ 1 := by
  intro h
  have h00 := congrArg (fun M : SL(2, F4) => (M : Matrix (Fin 2) (Fin 2) F4) 0 0) h
  revert h00
  decide

theorem pbEta_pow_three : pbEta ^ 3 = 1 := by
  decide +kernel

theorem pb_omega_fix : ∀ x : F4, F4.ω * x = x → x = 0 := by decide

theorem pb_omega_sq_fix : ∀ x : F4, F4.ω ^ 2 * x = x → x = 0 := by decide

theorem exists_eta : ∃ η : SL(2, F4), η ≠ 1 ∧ η ^ 3 = 1 ∧
    ∀ y ∈ YK, blockSL2 F4 3 2 η * y * (blockSL2 F4 3 2 η)⁻¹ = y → y = 1 := by
  refine ⟨pbEta, pbEta_ne_one, pbEta_pow_three, fun y hy hfix => ?_⟩
  obtain ⟨a₂, a₄, a₅, a₈, rfl⟩ := hy
  have hc := mul_inv_eq_iff_eq_mul.mp hfix
  have h20 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 2 0) hc
  have h21 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 2 1) hc
  have h30 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 3 0) hc
  have h31 := congrArg (fun M : SL(4, F4) => (M : Matrix (Fin 4) (Fin 4) F4) 3 1) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_pSL, pb_blockSL2_two] at h20 h21 h30 h31
  simp [pMat, pbEta, Matrix.mul_apply, Fin.sum_univ_four] at h20 h21 h30 h31
  have e4 : a₄ = 0 := pb_omega_fix a₄ (by linear_combination h20)
  have e2 : a₂ = 0 := pb_omega_fix a₂ (by linear_combination h21)
  have e8 : a₈ = 0 := pb_omega_sq_fix a₈ (by linear_combination h30)
  have e5 : a₅ = 0 := pb_omega_sq_fix a₅ (by linear_combination h31)
  subst e2 e4 e5 e8
  exact pSL_zero

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
