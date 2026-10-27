module

import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.ClassicalInvolution.Asc77.AscT7ML
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

set_option linter.unusedSectionVars false

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem map_conj_mul_eq {G : Type*} [Group G] {N : Subgroup G} {g b : G}
    (hb1 : ∀ n ∈ N, b * n * b⁻¹ ∈ N) (hb2 : ∀ n ∈ N, b⁻¹ * n * b ∈ N) :
    N.map (MulAut.conj (g * b)).toMonoidHom = N.map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨b * n * b⁻¹, hb1 n hn, by group⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨b⁻¹ * n * b, hb2 n hn, by group⟩

theorem coe_blockSL_zero (A : SL(2, F)) :
    ((blockSL F 4 2 0 (by norm_num) A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0, 0;
        (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0, 0;
        0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [CFSG.ClassicalInvolution.WeakCT.coe_blockSL, OuterL4.blockMat_four_zero]

theorem twin_std_k [Finite F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) {k : SL(4, F)} (hkR : k ∈ R)
    (hkk : proj 4 F k * proj 4 F k = proj 4 F x) :
    ∃ g : SL(4, F), R = (R0 F).map (MulAut.conj g).toMonoidHom ∧
      R' = (R0' F).map (MulAut.conj g).toMonoidHom ∧ x = g * x0 F * g⁻¹ ∧
      k = g * blockSL F 4 2 0 (by norm_num) r0 * g⁻¹ := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := OuterL4.twin_std h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hkR' := hkR
  rw [hRg] at hkR'
  obtain ⟨k₀, hk₀, hkeq⟩ := hkR'
  obtain ⟨k₂, rfl⟩ := hk₀
  have hk : k = g * blockSL F 4 2 0 (by norm_num) k₂ * g⁻¹ := by
    rw [← hkeq]
    rfl
  have hx : x = g * x0 F * g⁻¹ := hxg
  have hk0sq : proj 4 F (blockSL F 4 2 0 (by norm_num) k₂ * blockSL F 4 2 0 (by norm_num) k₂) =
      proj 4 F (x0 F) := by
    rw [hk, hx] at hkk
    simp only [map_mul, map_inv] at hkk ⊢
    have h3 : proj 4 F g * (proj 4 F (blockSL F 4 2 0 (by norm_num) k₂) *
        proj 4 F (blockSL F 4 2 0 (by norm_num) k₂)) * (proj 4 F g)⁻¹ =
        proj 4 F g * proj 4 F (x0 F) * (proj 4 F g)⁻¹ := by
      rw [← hkk]
      group
    exact mul_left_cancel (mul_right_cancel h3)
  obtain ⟨c, -, hc'⟩ := OuterL4.proj_eq_exists (n := 4) hk0sq
  obtain ⟨p, q, r, s, hK⟩ : ∃ p q r s : F, (k₂ : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, hK, coe_x0] at hc'
  have e00 := congrFun (congrFun hc' 0) 0
  have e01 := congrFun (congrFun hc' 0) 1
  have e10 := congrFun (congrFun hc' 1) 0
  have e11 := congrFun (congrFun hc' 1) 1
  have e22 := congrFun (congrFun hc' 2) 2
  simp at e00 e01 e10 e11 e22
  have hc1 : (c : F) = 1 := e22.symm
  rw [hc1, one_mul] at e00 e11
  have hK2 : (k₂ : Matrix (Fin 2) (Fin 2) F) * k₂ = -1 := by
    rw [hK]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -e00
    · linear_combination e01
    · linear_combination e10
    · linear_combination -e11
  obtain ⟨u, hu⟩ := exists_conj_r0 h2 k₂ hK2
  set b : SL(4, F) := blockSL F 4 2 0 (by norm_num) u with hb
  have hbR0 : b ∈ R0 F := ⟨u, rfl⟩
  have hbx : b * x0 F = x0 F * b := blockSL_zero_comm_x0 u
  have hbR0' : ∀ n ∈ R0' F, b * n = n * b := fun n hn => R0_comm_R0' hbR0 hn
  refine ⟨g * b, ?_, ?_, ?_, ?_⟩
  · rw [hRg, map_conj_mul_eq (N := R0 F) (fun n hn => (R0 F).mul_mem ((R0 F).mul_mem hbR0 hn)
      ((R0 F).inv_mem hbR0)) (fun n hn => (R0 F).mul_mem ((R0 F).mul_mem ((R0 F).inv_mem hbR0) hn)
      hbR0)]
    rfl
  · have h1 : ∀ n ∈ R0' F, b * n * b⁻¹ ∈ R0' F := fun n hn => by
      have : b * n * b⁻¹ = n := by rw [hbR0' n hn]; group
      rw [this]
      exact hn
    have h2' : ∀ n ∈ R0' F, b⁻¹ * n * b ∈ R0' F := fun n hn => by
      have : b⁻¹ * n * b = n := by
        rw [mul_assoc, ← hbR0' n hn, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact hn
    rw [hR'g, map_conj_mul_eq (N := R0' F) h1 h2']
    rfl
  · rw [hx]
    calc g * x0 F * g⁻¹ = g * (x0 F * b * b⁻¹) * g⁻¹ := by group
      _ = g * (b * x0 F * b⁻¹) * g⁻¹ := by rw [← hbx]
      _ = g * b * x0 F * (g * b)⁻¹ := by group
  · rw [hk]
    have hk2 : blockSL F 4 2 0 (by norm_num) k₂ =
        b * blockSL F 4 2 0 (by norm_num) r0 * b⁻¹ := by
      rw [hb, ← hu]
      simp only [map_mul, map_inv]
    rw [hk2]
    group

theorem autSq_data [Finite F] (h2 : (2 : F) ≠ 0) (α : MulAut (projectiveSL 4 F))
    (hfix : ∀ r ∈ R0 F, α (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ R0' F, α (proj 4 F r) = proj 4 F r)
    (hα : α * α = MulAut.conj (proj 4 F (x0 F))) :
    ∃ (A : GL (Fin 4) F) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ a * a = -(b * b) ∧
      (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] ∧
      α = conjAut 4 F A := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  have hx0 : x0 F = rootInv F (show 2 ≤ 4 by norm_num) := rfl
  have hrootcongr : MulAut.conj (proj 4 F (x0 F)) =
      conjAut 4 F (Matrix.SpecialLinearGroup.toGL (x0 F)) := (OuterL4.conjAut_toGL _).symm
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    have hfa : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
        (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r := fun r hr => by
      rw [← hαeq]
      exact hfix r hr
    have hfa' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range,
        (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r := fun r hr => by
      rw [← hαeq]
      exact hfix' r hr
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := OuterL4.aut_fix_blocks_zero h2 A σ hfa hfa'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hαeq
    rw [hαeq, hrootcongr, ← map_mul] at hα
    set X : GL (Fin 4) F := Matrix.SpecialLinearGroup.toGL (x0 F) with hX
    have h3 : conjAut 4 F (A * A * X⁻¹) = 1 := by rw [map_mul, hα, map_inv]; group
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp h3
    have h4 : (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
        (c : F) • (X : Matrix (Fin 4) (Fin 4) F) := by
      have h5 : A * A = Matrix.GeneralLinearGroup.scalar (Fin 4) c * X := by
        rw [hc]; group
      have h6 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h5
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul] at h6
      exact h6
    rw [hX, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hx0, coe_rootInv, OuterL4.negBlock_four,
      hM] at h4
    have e1 := congrFun (congrFun h4 0) 0
    have e2 := congrFun (congrFun h4 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e1 e2
    refine ⟨A, a, b, ha, hb, ?_, hM, hαeq⟩
    linear_combination e1 + e2
  · exfalso
    rw [pow_one] at hαeq
    have hfa : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
        (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r :=
      fun r hr => by
        rw [← hαeq]
        exact hfix r hr
    have hfa' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range,
        (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r :=
      fun r hr => by
        rw [← hαeq]
        exact hfix' r hr
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := OuterL4.aut_fix_blocks_one h2 A σ hfa hfa'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hαeq
    rw [hαeq, OuterL4.sq_of_antidiag A m n hm hn hM, hrootcongr] at hα
    have h3 : conjAut 4 F (Matrix.SpecialLinearGroup.toGL (x0 F)) = 1 := hα.symm
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mp h3
    have h6 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hx0, coe_rootInv, OuterL4.negBlock_four] at h6
    have e1 : (c : F) = -1 := by simpa using congrFun (congrFun h6 0) 0
    have e2 : (c : F) = 1 := by simpa using congrFun (congrFun h6 2) 2
    apply h2
    linear_combination e1 - e2

theorem exists_U (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * a = -(b * b))
    (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F) =
      !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) :
    ∃ U : GL (Fin 4) F,
      Matrix.SpecialLinearGroup.toGL (x0 F) * U = U * Matrix.SpecialLinearGroup.toGL (x0 F) ∧
      conjAut 4 F (Matrix.SpecialLinearGroup.toGL (blockSL F 4 2 0 (by norm_num) r0) * A) =
        conjAut 4 F U * conjAut 4 F (dGL 1) * (conjAut 4 F U)⁻¹ := by
  obtain ⟨i, hi, hai⟩ : ∃ i : F, i * i = -1 ∧ a = i * b := by
    refine ⟨a * b⁻¹, ?_, by field_simp⟩
    field_simp
    linear_combination hab
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hi
    exact one_ne_zero (neg_eq_zero.mp hi.symm)
  set Um : Matrix (Fin 4) (Fin 4) F := !![1, 1, 0, 0; -i, i, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] with hUm
  have hdet : Um.det ≠ 0 := by
    have : Um.det = 2 * i := by
      rw [hUm, Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
      ring
    rw [this]
    exact mul_ne_zero h2 hi0
  set U : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Um hdet with hU
  have hUcoe : (U : Matrix (Fin 4) (Fin 4) F) = Um := rfl
  refine ⟨U, ?_, ?_⟩
  · apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hUcoe, hUm, coe_x0]
    ext i' k
    fin_cases i' <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · have hMU : conjAut 4 F (Matrix.SpecialLinearGroup.toGL (blockSL F 4 2 0 (by norm_num) r0) *
        A * U) = conjAut 4 F (U * dGL 1) := by
      refine OuterL4.conjAut_eq_of_smul _ _ b hb ?_
      have hd1 : (dMat 1 : Matrix (Fin 4) (Fin 4) F) =
          !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
        ext i' k
        fin_cases i' <;> fin_cases k <;> simp [dMat, sgn]
      simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hUcoe, hUm,
        coe_blockSL_zero, hA, coe_dGL, coe_r0, hd1]
      ext i' k
      fin_cases i' <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
      all_goals
        try rw [hai]
        first | ring1 | linear_combination (-b) * hi | linear_combination b * hi
    have hM2 : conjAut 4 F (Matrix.SpecialLinearGroup.toGL (blockSL F 4 2 0 (by norm_num) r0) *
        A) * conjAut 4 F U = conjAut 4 F U * conjAut 4 F (dGL 1) := by
      rw [← map_mul, ← map_mul]
      exact hMU
    exact eq_mul_inv_of_mul_eq hM2

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4
