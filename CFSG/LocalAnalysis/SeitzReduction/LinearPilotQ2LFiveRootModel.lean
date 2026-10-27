module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.LieType.Chevalley

variable {k : Type} [Field k]

theorem transvection_zero_one_eq_unipU_three (b : k) :
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) b = unipU k b 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipU, Matrix.SpecialLinearGroup.transvection_coe]

theorem transvection_zero_two_eq_unipU_three (b : k) :
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) b = unipU k 0 0 b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipU, Matrix.SpecialLinearGroup.transvection_coe]

theorem transvection_one_two_eq_unipU_three (b : k) :
    SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) b = unipU k 0 b 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipU, Matrix.SpecialLinearGroup.transvection_coe]

theorem mem_projRad_zero_of_commute [Finite k] (hk : Nat.card k = 4) {z : projectiveSL 3 k}
    (h1 : proj 3 k (unipU k 1 0 0) * z = z * proj 3 k (unipU k 1 0 0))
    (h2 : proj 3 k (unipU k 0 0 1) * z = z * proj 3 k (unipU k 0 0 1)) : z ∈ projRad k 0 := by
  obtain ⟨Z, rfl⟩ := proj_surjective 3 k z
  have hc1 := commute_single_of_commute_proj (K := k) (n := 3) (i := 0) (j := 1) (Z := Z)
    (by decide) (by rw [transvection_zero_one_eq_unipU_three]; exact h1)
  have hc2 := commute_single_of_commute_proj (K := k) (n := 3) (i := 0) (j := 2) (Z := Z)
    (by decide) (by rw [transvection_zero_two_eq_unipU_three]; exact h2)
  have hz10 : (Z : Matrix (Fin 3) (Fin 3) k) 1 0 = 0 := by
    have h := congrFun (congrFun hc1.eq 0) 0
    simp [Matrix.mul_apply, Matrix.single_apply] at h
    exact h
  have hz11 : (Z : Matrix (Fin 3) (Fin 3) k) 1 1 = (Z : Matrix (Fin 3) (Fin 3) k) 0 0 := by
    have h := congrFun (congrFun hc1.eq 0) 1
    simp [Matrix.mul_apply, Matrix.single_apply] at h
    exact h
  have hz12 : (Z : Matrix (Fin 3) (Fin 3) k) 1 2 = 0 := by
    have h := congrFun (congrFun hc1.eq 0) 2
    simp [Matrix.mul_apply, Matrix.single_apply] at h
    exact h
  have hz20 : (Z : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 := by
    have h := congrFun (congrFun hc2.eq 0) 0
    simp [Matrix.mul_apply, Matrix.single_apply] at h
    exact h
  have hz21 : (Z : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
    have h := congrFun (congrFun hc2.eq 0) 1
    simp [Matrix.mul_apply, Matrix.single_apply] at h
    exact h
  have hz22 : (Z : Matrix (Fin 3) (Fin 3) k) 2 2 = (Z : Matrix (Fin 3) (Fin 3) k) 0 0 := by
    have h := congrFun (congrFun hc2.eq 0) 2
    simp [Matrix.mul_apply, Matrix.single_apply] at h
    exact h
  have hdet : (Z : Matrix (Fin 3) (Fin 3) k) 0 0 * (Z : Matrix (Fin 3) (Fin 3) k) 0 0 *
      (Z : Matrix (Fin 3) (Fin 3) k) 0 0 = 1 := by
    have h := Z.prop
    rw [Matrix.det_fin_three, hz10, hz11, hz12, hz20, hz21, hz22] at h
    linear_combination h
  have hμ : (Z : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  obtain ⟨g', hg', hg'e⟩ := exists_proj_eq_scalar_mul hk hμ
  refine mem_projRad_zero.2 ⟨((Z : Matrix (Fin 3) (Fin 3) k) 0 0)⁻¹ *
    (Z : Matrix (Fin 3) (Fin 3) k) 0 1, ((Z : Matrix (Fin 3) (Fin 3) k) 0 0)⁻¹ *
    (Z : Matrix (Fin 3) (Fin 3) k) 0 2, ?_⟩
  rw [← hg']
  congr 1
  ext i j
  rw [hg'e, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp [hz10, hz11, hz12, hz20, hz21, hz22, hμ]

variable (k) in
@[expose] def projRootU : Subgroup (projectiveSL 3 k) :=
  (sl2Unip k).map (leviProj k 0)

theorem mem_projRootU {x : projectiveSL 3 k} :
    x ∈ projRootU k ↔ ∃ b : k, proj 3 k (unipU k 0 b 0) = x := by
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, by rw [← leviOne_uSL]; rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, by rw [← leviOne_uSL]; rfl⟩

theorem projRootU_le_normalizer :
    projRootU k ≤ normalizer (projRad k 0 : Set (projectiveSL 3 k)) := by
  rintro _ ⟨B, -, rfl⟩
  exact leviOne_mem_normalizer B

theorem card_projRootU [Finite k] : Nat.card (projRootU k) = Nat.card k := by
  rw [projRootU, Subgroup.card_map_of_injective (leviProj_injective 0), card_sl2Unip]

theorem mul_self_of_mem_projRootU [CharP k 2] {x : projectiveSL 3 k} (hx : x ∈ projRootU k) :
    x * x = 1 := by
  obtain ⟨b, rfl⟩ := mem_projRootU.1 hx
  rw [← map_mul, unipU_mul]
  simp only [CharTwo.add_self_eq_zero, zero_mul, unipU_zero, map_one]

theorem eq_one_of_mem_projRootU_of_commute {x : projectiveSL 3 k} (hx : x ∈ projRootU k)
    (h : x * proj 3 k (unipU k 1 0 0) = proj 3 k (unipU k 1 0 0) * x) : x = 1 := by
  obtain ⟨b, rfl⟩ := mem_projRootU.1 hx
  rw [← map_mul, ← map_mul, unipU_mul, unipU_mul] at h
  obtain ⟨-, -, h3⟩ := unipU_eq_of_proj_eq h
  have hb : b = 0 := by linear_combination -h3
  rw [hb, unipU_zero, map_one]

theorem fieldAut_three_proj_unipU (σ : k ≃+* k) (a b c : k) :
    fieldAut 3 k σ (proj 3 k (unipU k a b c)) = proj 3 k (unipU k (σ a) (σ b) (σ c)) := by
  rw [fieldAut_proj]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipU, SpecialLinearGroup.map_apply_coe]

theorem fieldAut_mem_projRootU (σ : k ≃+* k) {x : projectiveSL 3 k} (hx : x ∈ projRootU k) :
    fieldAut 3 k σ x ∈ projRootU k := by
  obtain ⟨b, rfl⟩ := mem_projRootU.1 hx
  rw [fieldAut_three_proj_unipU, map_zero]
  exact mem_projRootU.2 ⟨σ b, rfl⟩

theorem coe_blockSLEquiv_transvection {n m : ℕ} {R : Type*} [Field R] (N : Finset (Fin n))
    (eN : N ≃ Fin m) {p q : Fin m} (hpq : p ≠ q) (hpq' : ((eN.symm p : N) : Fin n) ≠ eN.symm q)
    (b : R) :
    ((blockSLEquiv N eN (SpecialLinearGroup.transvection hpq b) : blockSpecialLinear (K := R) N) :
      SpecialLinearGroup (Fin n) R) = SpecialLinearGroup.transvection hpq' b := by
  ext i j
  rw [coe_blockSLEquiv_apply]
  by_cases h : i ∈ N ∧ j ∈ N
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
    have hi : p = eN ⟨i, h.1⟩ ↔ ((eN.symm p : N) : Fin n) = i := by
      constructor
      · intro e'
        rw [e', Equiv.symm_apply_apply]
      · intro e'
        have he : eN.symm p = ⟨i, h.1⟩ := Subtype.ext e'
        rw [← he, Equiv.apply_symm_apply]
    have hj : q = eN ⟨j, h.2⟩ ↔ ((eN.symm q : N) : Fin n) = j := by
      constructor
      · intro e'
        rw [e', Equiv.symm_apply_apply]
      · intro e'
        have he : eN.symm q = ⟨j, h.2⟩ := Subtype.ext e'
        rw [← he, Equiv.apply_symm_apply]
    have h1 : (1 : Matrix (Fin m) (Fin m) R) (eN ⟨i, h.1⟩) (eN ⟨j, h.2⟩) =
        (1 : Matrix (Fin n) (Fin n) R) i j := by
      simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
    rw [h1]
    simp only [hi, hj]
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
    have hnot : ¬ (((eN.symm p : N) : Fin n) = i ∧ ((eN.symm q : N) : Fin n) = j) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨(eN.symm p).2, (eN.symm q).2⟩
    simp [hnot]

end CFSG.SeitzReduction.LinearPilot
