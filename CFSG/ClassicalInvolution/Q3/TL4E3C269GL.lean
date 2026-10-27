module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Y
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3C269G

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

section GL2

variable {K : Type} [Field K]

@[expose] noncomputable def diagOneNeg (K : Type) [Field K] : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by simp [Matrix.det_fin_two_of])

theorem coe_diagOneNeg :
    ((diagOneNeg K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, -1] :=
  rfl

theorem entries_of_involution {A : GL (Fin 2) K} (hA2 : A * A = 1) (hA1 : A ≠ 1)
    (hAm : A ≠ -1) :
    (A : Matrix (Fin 2) (Fin 2) K) 1 1 = -(A : Matrix (Fin 2) (Fin 2) K) 0 0 ∧
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := Matrix.eta_fin_two M
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have hMM : M * M = 1 := by rw [hMdef, ← Units.val_mul, hA2, Units.val_one]
  rw [hM, Matrix.mul_fin_two, Matrix.one_fin_two] at hMM
  have e00 : a * a + b * c = 1 := by simpa using congrFun (congrFun hMM 0) 0
  have e01 : a * b + b * d = 0 := by simpa using congrFun (congrFun hMM 0) 1
  have e10 : c * a + d * c = 0 := by simpa using congrFun (congrFun hMM 1) 0
  have e11 : c * b + d * d = 1 := by simpa using congrFun (congrFun hMM 1) 1
  refine ⟨?_, e00⟩
  by_contra hne
  have hs : a + d ≠ 0 := fun h => hne (by linear_combination h)
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hs
  have had : a = d := by
    have : (a - d) * (a + d) = 0 := by
      rw [hb] at e00
      rw [hc] at e11
      linear_combination e00 - e11
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
  have ha2 : (a - 1) * (a + 1) = 0 := by
    rw [hb] at e00
    linear_combination e00
  rcases mul_eq_zero.mp ha2 with ha | ha
  · apply hA1
    apply Units.ext
    rw [← hMdef, hM, Units.val_one, Matrix.one_fin_two]
    rw [← had, sub_eq_zero.mp ha, hb, hc]
  · apply hAm
    apply Units.ext
    rw [← hMdef, hM, Units.val_neg, Units.val_one, ← had, eq_neg_of_add_eq_zero_left ha, hb, hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem exists_conj_diagOneNeg (h2 : (2 : K) ≠ 0) {A : GL (Fin 2) K} (hA2 : A * A = 1)
    (hA1 : A ≠ 1) (hAm : A ≠ -1) : ∃ U : GL (Fin 2) K, A * U = U * diagOneNeg K := by
  obtain ⟨htr, e00⟩ := entries_of_involution hA2 hA1 hAm
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := Matrix.eta_fin_two M
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have hbc : b * c = 1 - a * a := by linear_combination e00
  have key : ∀ U : Matrix (Fin 2) (Fin 2) K, U.det ≠ 0 →
      M * U = U * !![1, 0; 0, -1] → ∃ U' : GL (Fin 2) K, A * U' = U' * diagOneNeg K := by
    intro U hU hMU
    refine ⟨GeneralLinearGroup.mkOfDetNeZero U hU, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, coe_diagOneNeg]
    exact hMU
  by_cases hb0 : b = 0
  · have ha2 : (a - 1) * (a + 1) = 0 := by
      rw [hb0] at e00
      linear_combination e00
    rcases mul_eq_zero.mp ha2 with ha | ha
    · have ha' : a = 1 := sub_eq_zero.mp ha
      refine key !![2, 0; c, 1] (by simpa [Matrix.det_fin_two_of] using h2) ?_
      rw [hM, Matrix.mul_fin_two, Matrix.mul_fin_two, htr, ha', hb0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      ring
    · have ha' : a = -1 := eq_neg_of_add_eq_zero_left ha
      refine key !![0, 2; 1, -c] (by simpa [Matrix.det_fin_two_of] using h2) ?_
      rw [hM, Matrix.mul_fin_two, Matrix.mul_fin_two, htr, ha', hb0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      ring
  · refine key !![b, b; 1 - a, -1 - a] ?_ ?_
    · rw [Matrix.det_fin_two_of]
      intro h
      apply hb0
      have : (2 : K) * b = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left h2
    · rw [hM, Matrix.mul_fin_two, Matrix.mul_fin_two, htr]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · ring
      · ring
      · linear_combination hbc
      · linear_combination hbc

end GL2

section L3

variable {K : Type} [Field K]

theorem coe_blockSL_zero_neg_one :
    ((WeakCT.blockSL K 3 2 0 (by omega) (-1) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![-1, -1, 1] := by
  rw [WeakCT.coe_blockSL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Phan.blockMat, Phan.blockSel, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_blockSL_one_neg_one :
    ((WeakCT.blockSL K 3 2 1 (by omega) (-1) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![1, -1, -1] := by
  rw [WeakCT.coe_blockSL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Phan.blockMat, Phan.blockSel, Matrix.mul_apply, Fin.sum_univ_two]

theorem blkP_one_neg_one :
    blkP 1 (-1 : GL (Fin 2) K) = WeakCT.blockSL K 3 2 0 (by omega) (-1) := by
  apply Subtype.ext
  rw [coe_blockSL_zero_neg_one, MF163.L3.coe_blkP_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Lemma41aL3.blkMat, Matrix.det_fin_two]

theorem blkP_one_diagOneNeg :
    blkP 1 (diagOneNeg K) = WeakCT.blockSL K 3 2 1 (by omega) (-1) := by
  apply Subtype.ext
  rw [coe_blockSL_one_neg_one, MF163.L3.coe_blkP_one, coe_diagOneNeg]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Lemma41aL3.blkMat, Matrix.det_fin_two_of]

theorem mul_neg_one_comm (A : SL(2, K)) : A * (-1) = (-1) * A :=
  Subtype.ext (by simp)

theorem map_range_le_centralizer {i : ℕ} (hi : i + 2 ≤ 3) :
    (WeakCT.blockSL K 3 2 i hi).range.map (proj 3 K) ≤
      Subgroup.centralizer ({proj 3 K (WeakCT.blockSL K 3 2 i hi (-1))} : Set _) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    mul_neg_one_comm]

theorem sup_centralizer_blocks :
    Subgroup.centralizer ({proj 3 K (WeakCT.blockSL K 3 2 0 (by omega) (-1))} :
        Set (projectiveSL 3 K)) ⊔
      Subgroup.centralizer ({proj 3 K (WeakCT.blockSL K 3 2 1 (by omega) (-1))} :
        Set (projectiveSL 3 K)) = ⊤ := by
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective (proj 3 K) (proj_surjective 3 K),
    ← WeakCT.B12_sup_B23, Subgroup.map_sup]
  exact sup_le_sup (map_range_le_centralizer _) (map_range_le_centralizer _)

theorem proj_blkP_scalar_cube (Q : GL (Fin 3) K) {ω : Kˣ} (hω : ω ^ 3 = 1) :
    proj 3 K (blkP Q (GeneralLinearGroup.scalar (Fin 2) ω)) = 1 := by
  have h := MF163.L3.conjAut_inv_proj_blkP Q (GeneralLinearGroup.scalar (Fin 2) ω)
  rw [MF163.L3.proj_blkP_scalar_cube hω] at h
  have h' := congrArg (conjAut 3 K Q) h
  rwa [MulAut.apply_inv_self, map_one] at h'

variable [Finite K]

theorem sup_centralizer_eq_top_psl3 (hodd : Odd (Nat.card K)) {t s : projectiveSL 3 K}
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hts : t * s = s * t) (hne : t ≠ s) :
    Subgroup.centralizer ({t} : Set (projectiveSL 3 K)) ⊔
      Subgroup.centralizer ({s} : Set (projectiveSL 3 K)) = ⊤ := by
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ :=
    exists_frame hodd (Subgroup.topEquiv (G := projectiveSL 3 K)) (Subgroup.mem_top t) ht
  have hπQ : ∀ A, π A = proj 3 K (blkP Q (A : GL (Fin 2) K)) := fun A => hπ A
  have hsC : s ∈ π.range := by
    rw [hrange]
    exact ⟨Subgroup.mem_top s, Subgroup.mem_centralizer_singleton_iff.mpr hts.symm⟩
  obtain ⟨A₀, hA₀⟩ := hsC
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  obtain ⟨ω, hω3, hω⟩ := hk (A₀ * A₀) (by rw [map_mul, hA₀, hs2])
  set A : GL (Fin 2) K := (A₀ : GL (Fin 2) K) * GeneralLinearGroup.scalar (Fin 2) ω with hAdef
  have hπA : proj 3 K (blkP Q A) = s := by
    rw [hAdef, map_mul, map_mul, proj_blkP_scalar_cube Q hω3, mul_one, ← hπQ, hA₀]
  have hA2 : A * A = 1 := by
    have hω' : (A₀ : GL (Fin 2) K) * A₀ = GeneralLinearGroup.scalar (Fin 2) ω := hω
    have hc := scalar_mul_comm ω (A₀ : GL (Fin 2) K)
    calc A * A = (A₀ : GL (Fin 2) K) * (GeneralLinearGroup.scalar (Fin 2) ω * A₀) *
          GeneralLinearGroup.scalar (Fin 2) ω := by rw [hAdef]; group
      _ = (A₀ : GL (Fin 2) K) * A₀ * GeneralLinearGroup.scalar (Fin 2) ω *
          GeneralLinearGroup.scalar (Fin 2) ω := by rw [hc]; group
      _ = GeneralLinearGroup.scalar (Fin 2) (ω * ω * ω) := by rw [hω', map_mul, map_mul]
      _ = 1 := by rw [← pow_three', hω3, map_one]
  have htQ : t = proj 3 K (blkP Q (-1)) := by
    rw [← hπ1]
    exact hπQ _
  have hA1 : A ≠ 1 := by
    intro h
    rw [h, map_one, map_one] at hπA
    rw [← hπA, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hAm : A ≠ -1 := fun h => hne (htQ.trans (by rw [← h, hπA]))
  obtain ⟨U, hU⟩ := exists_conj_diagOneNeg h2 hA2 hA1 hAm
  set c := proj 3 K (blkP Q U) with hcdef
  have hct : c * t = t * c := by
    rw [htQ, hcdef, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    rw [mul_neg_one, neg_one_mul]
  have hct' : c⁻¹ * t = t * c⁻¹ :=
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
      _ = t * c⁻¹ := by group
  have hsc : s = c * proj 3 K (blkP Q (diagOneNeg K)) * c⁻¹ := by
    rw [← hπA, hcdef, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    rw [← hU]
    group
  rw [hsc]
  refine sup_centralizer_eq_top_of_conj hct' ?_
  rw [show c⁻¹ * (c * proj 3 K (blkP Q (diagOneNeg K)) * c⁻¹) * c⁻¹⁻¹ =
    proj 3 K (blkP Q (diagOneNeg K)) by group]
  refine sup_centralizer_eq_top_of_equiv (conjAut 3 K Q)⁻¹ ?_
  rw [htQ, MF163.L3.conjAut_inv_proj_blkP, MF163.L3.conjAut_inv_proj_blkP, blkP_one_neg_one,
    blkP_one_diagOneNeg]
  exact sup_centralizer_blocks

end L3

end CFSG.ClassicalInvolution.Q3.TL4.E3C269G
