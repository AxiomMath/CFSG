module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPFieldBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalSubfield
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveDTransfer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section YTwo

variable {F : Type*} [Field F]

@[expose] def yTwoMat : SpecialLinearGroup (Fin 4) F :=
  SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 2 by decide) 1 *
    SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 3 by decide) 1

theorem coe_yTwoMat :
    ((yTwoMat : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 + single 0 2 1 + single 1 3 1 := by
  rw [yTwoMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.one_apply, single_apply]

theorem unitri_mul_yTwo {u : SpecialLinearGroup (Fin 4) F} (hu : u ∈ unitriangular 4 F) :
    u * yTwoMat = SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 3 by decide)
      ((u : Matrix (Fin 4) (Fin 4) F) 0 1 - (u : Matrix (Fin 4) (Fin 4) F) 2 3) * yTwoMat * u := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hu
  have h10 := hlow 1 0 (by decide)
  have h20 := hlow 2 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h30 := hlow 3 0 (by decide)
  have h31 := hlow 3 1 (by decide)
  have h32 := hlow 3 2 (by decide)
  have h00 := hdiag 0
  have h11 := hdiag 1
  have h22 := hdiag 2
  have h33 := hdiag 3
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_yTwoMat, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.one_apply, single_apply,
      h10, h20, h21, h30, h31, h32, h00, h11, h22, h33] <;> ring

theorem yTwoMat_mul_self [CharP F 2] : (yTwoMat : SpecialLinearGroup (Fin 4) F) * yTwoMat = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_yTwoMat, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.one_apply, single_apply] <;>
    linear_combination h2

variable (F) in
@[expose] noncomputable def yTwo : projectiveSL 4 F :=
  proj 4 F yTwoMat

theorem yTwo_mul_self [CharP F 2] : yTwo F * yTwo F = 1 := by
  rw [yTwo, ← map_mul, yTwoMat_mul_self, map_one]

theorem xab_mul_self_of_charTwo [CharP F 2] {n : ℕ} {a b : Fin n} (hab : a ≠ b) (c : F) :
    xab hab c * xab hab c = 1 := by
  rw [← xab_add, CharTwo.add_self_eq_zero, xab_zero]

theorem card_rootGroup_le_card_field [Finite F] {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    Nat.card (rootGroup (K := F) hab) ≤ Nat.card F := by
  have h := Nat.card_le_card_of_surjective _
    ((proj n F).comp (SpecialLinearGroup.transvectionHom hab)).rangeRestrict_surjective
  rw [rootGroup]
  exact h.trans_eq (Nat.card_congr Multiplicative.toAdd)

theorem commutator_yTwo_mem_rootGroup {u : projectiveSL 4 F} (hu : u ∈ projUnitriangular 4 F) :
    u * yTwo F * u⁻¹ * (yTwo F)⁻¹ ∈ rootGroup (K := F) (show (0 : Fin 4) ≠ 3 by decide) := by
  obtain ⟨U, hU, rfl⟩ := hu
  rw [mem_rootGroup]
  refine ⟨(U : Matrix (Fin 4) (Fin 4) F) 0 1 - (U : Matrix (Fin 4) (Fin 4) F) 2 3, ?_⟩
  have h := congrArg (proj 4 F) (unitri_mul_yTwo hU)
  rw [map_mul, map_mul, map_mul] at h
  rw [xab, yTwo, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, ← h]

theorem card_pow_five_le_card_inf_centralizer_yTwo [Finite F] [CharP F 2] :
    Nat.card F ^ 5 ≤
      Nat.card (projUnitriangular 4 F ⊓ centralizer ({yTwo F} : Set (projectiveSL 4 F)) :
        Subgroup (projectiveSL 4 F)) := by
  have hW2 : ∀ w ∈ rootGroup (K := F) (show (0 : Fin 4) ≠ 3 by decide), w * w = 1 := by
    intro w hw
    obtain ⟨c, rfl⟩ := (mem_rootGroup _).1 hw
    exact xab_mul_self_of_charTwo _ c
  have h := card_le_card_inf_centralizer_mul_card_of_exponent_two hW2 yTwo_mul_self
    (P := projUnitriangular 4 F) fun y hy => commutator_yTwo_mem_rootGroup hy
  rw [card_projUnitriangular] at h
  have hW : Nat.card (rootGroup (K := F) (show (0 : Fin 4) ≠ 3 by decide) ⊓
      centralizer ({yTwo F} : Set (projectiveSL 4 F)) : Subgroup (projectiveSL 4 F)) ≤
      Nat.card F :=
    (Subgroup.card_le_of_le inf_le_left).trans (card_rootGroup_le_card_field _)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have h6 : Nat.card F ^ (4 * (4 - 1) / 2) = Nat.card F ^ 5 * Nat.card F := by
    norm_num [pow_succ]
  rw [h6] at h
  exact le_of_mul_le_mul_right (h.trans (Nat.mul_le_mul_left _ hW)) hpos

end YTwo

section Map

variable {K F : Type*} [Field K] [Field F]

theorem specialLinearGroup_map_transvection (ι : K →+* F) {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (c : K) :
    SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection hab (ι c) := by
  apply Subtype.ext
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_apply, Matrix.add_apply, single_apply, single_apply, Matrix.one_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem projMap_xab_one (ι : K →+* F) {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    projMap n ι (xab hab 1) = xab hab 1 := by
  rw [xab, projMap_proj, specialLinearGroup_map_transvection, map_one, xab]

theorem projMap_yTwo (ι : K →+* F) : projMap 4 ι (yTwo K) = yTwo F := by
  rw [yTwo, projMap_proj, yTwoMat, map_mul, specialLinearGroup_map_transvection,
    specialLinearGroup_map_transvection, map_one, yTwo, yTwoMat]

end Map

section NormalForm

variable {F : Type*} [Field F]

theorem InvPlacement.nil_two {n : ℕ} (P : InvPlacement n 2) :
    P.nil F = single (P.u 0) (P.w 0) 1 + single (P.u 1) (P.w 1) 1 := by
  ext i j
  rw [InvPlacement.nil, Matrix.of_apply, Matrix.add_apply, single_apply, single_apply]
  by_cases h0 : P.u 0 = i ∧ P.w 0 = j
  · have h1 : ¬ (P.u 1 = i ∧ P.w 1 = j) := fun h1 =>
      P.u_injective.ne (show (0 : Fin 2) ≠ 1 by decide) (h0.1.trans h1.1.symm)
    rw [ite_eq_left ⟨0, h0⟩, ite_eq_left h0, ite_eq_right h1, add_zero]
  · by_cases h1 : P.u 1 = i ∧ P.w 1 = j
    · rw [ite_eq_left ⟨1, h1⟩, ite_eq_right h0, ite_eq_left h1, zero_add]
    · have hn : ¬ ∃ a, P.u a = i ∧ P.w a = j := by
        rintro ⟨a, ha⟩
        fin_cases a
        exacts [h0 ha, h1 ha]
      rw [ite_eq_right hn, ite_eq_right h0, ite_eq_right h1, add_zero]

theorem InvPlacement.mat_eq_transvection_mul_transvection {n : ℕ} (P : InvPlacement n 2) :
    P.mat F = SpecialLinearGroup.transvection (P.u_ne_w 0 0) 1 *
      SpecialLinearGroup.transvection (P.u_ne_w 1 1) 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, InvPlacement.coe_mat,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    InvPlacement.nil_two, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne (1 : F) (P.u 0) (P.w 0) (P.u 1) (P.u_ne_w 1 0).symm, add_zero]
  abel

theorem InvPlacement.mat_eq_one_of_zero {n : ℕ} (P : InvPlacement n 0) : P.mat F = 1 := by
  apply Subtype.ext
  rw [InvPlacement.coe_mat, Matrix.SpecialLinearGroup.coe_one]
  have h0 : P.nil F = 0 := by
    ext i j
    rw [InvPlacement.nil, Matrix.of_apply, ite_eq_right_iff.2 (fun ⟨a, _⟩ => a.elim0),
      Matrix.zero_apply]
  rw [h0, add_zero]

@[expose] noncomputable def InvPlacement.permFour (P : InvPlacement 4 2) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![P.u 0, P.u 1, P.w 0, P.w 1] (Finite.injective_iff_bijective.1 (by
    have hu01 : P.u 0 ≠ P.u 1 := P.u_injective.ne (by decide)
    have hw01 : P.w 0 ≠ P.w 1 := P.w_injective.ne (by decide)
    have h00 := P.u_ne_w 0 0
    have h01 := P.u_ne_w 0 1
    have h10 := P.u_ne_w 1 0
    have h11 := P.u_ne_w 1 1
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all))

theorem InvPlacement.permFour_symm (P : InvPlacement 4 2) :
    P.permFour.symm (P.u 0) = 0 ∧ P.permFour.symm (P.u 1) = 1 ∧ P.permFour.symm (P.w 0) = 2 ∧
      P.permFour.symm (P.w 1) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Equiv.symm_apply_eq] <;> rfl

variable [CharP F 2]

theorem InvPlacement.conj_elt_eq_yTwo (P : InvPlacement 4 2) :
    proj 4 F (permSL P.permFour) * P.elt F * (proj 4 F (permSL P.permFour))⁻¹ = yTwo F := by
  obtain ⟨h0, h1, h2, h3⟩ := P.permFour_symm
  rw [InvPlacement.elt, yTwo, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [P.mat_eq_transvection_mul_transvection, yTwoMat]
  have e : permSL P.permFour * (SpecialLinearGroup.transvection (P.u_ne_w 0 0) (1 : F) *
      SpecialLinearGroup.transvection (P.u_ne_w 1 1) 1) * (permSL P.permFour)⁻¹ =
      (permSL P.permFour * SpecialLinearGroup.transvection (P.u_ne_w 0 0) (1 : F) *
        (permSL P.permFour)⁻¹) * (permSL P.permFour *
          SpecialLinearGroup.transvection (P.u_ne_w 1 1) 1 * (permSL P.permFour)⁻¹) := by
    group
  rw [e, permSL_mul_transvection_mul_inv, permSL_mul_transvection_mul_inv,
    transvection_congr _ (show (0 : Fin 4) ≠ 2 by decide) h0 h2,
    transvection_congr _ (show (1 : Fin 4) ≠ 3 by decide) h1 h3]

end NormalForm

section Four

variable {K F : Type*} [Field K] [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem isPGroup_projUnitriangular_four (hF : Nat.card F = 4) :
    IsPGroup 2 (projUnitriangular 4 F) ∧ Nat.card (projUnitriangular 4 F) = 2 ^ 12 := by
  have hc : Nat.card (projUnitriangular 4 F) = 2 ^ 12 := by
    rw [card_projUnitriangular, hF]
    norm_num
  exact ⟨IsPGroup.of_card hc, hc⟩

theorem exists_conj_eq_projMap_of_mul_self (hF : Nat.card F = 4) (ι : K →+* F)
    {z : projectiveSL 4 F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ (c : projectiveSL 4 F) (z₀ : projectiveSL 4 K) (R : Subgroup (projectiveSL 4 F)),
      c * z * c⁻¹ = projMap 4 ι z₀ ∧ R ≤ centralizer ({projMap 4 ι z₀} : Set _) ∧
        IsPGroup 2 R ∧ 2 ^ 10 ≤ Nat.card R := by
  obtain ⟨hU2, hUc⟩ := isPGroup_projUnitriangular_four (F := F) hF
  obtain ⟨k, P, c₁, hc₁⟩ := exists_conj_eq_elt hz
  have hk : k ≤ 2 := by
    have h := Fintype.card_le_of_injective P.supp P.supp_injective
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  interval_cases k
  ·
    exfalso
    apply hz1
    rw [InvPlacement.elt, P.mat_eq_one_of_zero, map_one] at hc₁
    have h1 : z = c₁⁻¹ * (c₁ * z * c₁⁻¹) * c₁ := by group
    rw [h1, hc₁]
    group
  ·
    have hn : 2 ≤ 4 := by norm_num
    obtain ⟨c₂, hc₂⟩ := exists_conj_xab_eq_xab (K := F) (P.u_ne_w 0 0) (firstIdx_ne_lastIdx hn) 1
    have hP : P.elt F = xab (P.u_ne_w 0 0) 1 := by
      rw [InvPlacement.elt, P.mat_eq_transvection]
      rfl
    refine ⟨c₂ * c₁, xab (K := K) (firstIdx_ne_lastIdx hn) 1, projUnitriangular 4 F, ?_, ?_,
      hU2, ?_⟩
    · rw [projMap_xab_one, ← hc₂, ← hP, ← hc₁]
      group
    · intro u hu
      rw [projMap_xab_one, mem_centralizer_singleton_iff]
      exact xab_first_last_mul_comm hn 1 hu
    · rw [hUc]
      norm_num
  ·
    refine ⟨proj 4 F (permSL P.permFour) * c₁, yTwo K,
      projUnitriangular 4 F ⊓ centralizer ({yTwo F} : Set (projectiveSL 4 F)), ?_, ?_, ?_, ?_⟩
    · rw [projMap_yTwo, ← P.conj_elt_eq_yTwo, ← hc₁]
      group
    · rw [projMap_yTwo]
      exact inf_le_right
    · exact hU2.to_le inf_le_left
    · have h := card_pow_five_le_card_inf_centralizer_yTwo (F := F)
      rw [hF] at h
      calc 2 ^ 10 = 4 ^ 5 := by norm_num
        _ ≤ _ := h

end Four

end CFSG.SeitzReduction.LinearPilot
