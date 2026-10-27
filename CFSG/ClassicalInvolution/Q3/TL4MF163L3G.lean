module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3A
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem eq_blk_scalar_of_fix [Finite K] (h4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0)
    {A : GL (Fin 3) K}
    (h : ∀ B : SL(2, K), conjAut 3 K A (proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) =
      proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) :
    ∃ ν ν' : Kˣ, (A : Matrix (Fin 3) (Fin 3) K) =
      Lemma41aL3.blkMat ((ν : K) • (1 : Matrix (Fin 2) (Fin 2) K)) (ν' : K) := by
  have : Group.IsPerfect SL(2, K) := sl2_isPerfect h4
  have hker : (proj 3 K).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj, scalars_eq_center]
  let φ : SL(2, K) →* SL(3, K) := (blkP 1).comp SpecialLinearGroup.toGL
  let β : SL(3, K) →* SL(3, K) :=
    (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A).toMonoidHom
  have heq : β.comp φ = φ := LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker
    (MonoidHom.ext fun B => by
      show proj 3 K (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
        (blkP 1 (SpecialLinearGroup.toGL B))) = proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))
      rw [← conjAut_proj]
      exact h B)
  have hcomm : ∀ B : SL(2, K), (A : Matrix (Fin 3) (Fin 3) K) *
      Lemma41aL3.blkMat (B : Matrix (Fin 2) (Fin 2) K) 1 =
        Lemma41aL3.blkMat (B : Matrix (Fin 2) (Fin 2) K) 1 * A := by
    intro B
    have h1 := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K))
      (DFunLike.congr_fun heq B)
    have hB : ((SpecialLinearGroup.toGL B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (B : Matrix (Fin 2) (Fin 2) K) := rfl
    have hdB : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := B.2
    simp only [MonoidHom.comp_apply, β, φ, MulEquiv.coe_toMonoidHom] at h1
    rw [coe_slConjugation, coe_blkP_one, hB, hdB, inv_one] at h1
    calc (A : Matrix (Fin 3) (Fin 3) K) * Lemma41aL3.blkMat (B : Matrix (Fin 2) (Fin 2) K) 1
        = (A : Matrix (Fin 3) (Fin 3) K) * Lemma41aL3.blkMat (B : Matrix (Fin 2) (Fin 2) K) 1 *
            (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = Lemma41aL3.blkMat (B : Matrix (Fin 2) (Fin 2) K) 1 * A := by
          rw [← mul_assoc, h1]
  have hneg := hcomm (-1)
  have hneg' : Lemma41aL3.blkMat (((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) 1 =
      diagonal ![-1, -1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]
  rw [hneg'] at hneg
  obtain ⟨h02, h12, h20, h21⟩ := block_eq_zero_of_commute_negDiag h2 hneg
  set M := (A : Matrix (Fin 3) (Fin 3) K) with hM
  let X : Matrix (Fin 2) (Fin 2) K := !![M 0 0, M 0 1; M 1 0, M 1 1]
  have hX : X ∈ Set.range (Matrix.scalar (Fin 2)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun T => ?_
    have hT := hcomm T.toSpecialLinearGroup
    rw [TransvectionStruct.toSpecialLinearGroup_coe] at hT
    have e := fun i j => congrFun (congrFun hT i) j
    have hT' : T.toMatrix = !![T.toMatrix 0 0, T.toMatrix 0 1; T.toMatrix 1 0, T.toMatrix 1 1] :=
      Matrix.eta_fin_two _
    show T.toMatrix * X = X * T.toMatrix
    rw [hT']
    ext i j
    fin_cases i <;> fin_cases j
    · have := e 0 0
      simp [X, Lemma41aL3.blkMat, Matrix.mul_apply, Fin.sum_univ_three, h02, h20] at this ⊢
      linear_combination -this
    · have := e 0 1
      simp [X, Lemma41aL3.blkMat, Matrix.mul_apply, Fin.sum_univ_three, h02, h21] at this ⊢
      linear_combination -this
    · have := e 1 0
      simp [X, Lemma41aL3.blkMat, Matrix.mul_apply, Fin.sum_univ_three, h12, h20] at this ⊢
      linear_combination -this
    · have := e 1 1
      simp [X, Lemma41aL3.blkMat, Matrix.mul_apply, Fin.sum_univ_three, h12, h21] at this ⊢
      linear_combination -this
  obtain ⟨ν, hν⟩ := hX
  have hdet : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  have e00 : M 0 0 = ν := by
    have := congrFun (congrFun hν 0) 0; simp [X] at this; exact this.symm
  have e01 : M 0 1 = 0 := by
    have := congrFun (congrFun hν 0) 1; simp [X] at this; exact this.symm
  have e10 : M 1 0 = 0 := by
    have := congrFun (congrFun hν 1) 0; simp [X] at this; exact this.symm
  have e11 : M 1 1 = ν := by
    have := congrFun (congrFun hν 1) 1; simp [X] at this; exact this.symm
  have hdet' : M.det = ν * ν * M 2 2 := by
    rw [Matrix.det_fin_three, e00, e01, e10, e11, h02, h12, h20, h21]
    ring
  have hν0 : ν ≠ 0 := fun h => hdet (by rw [hdet', h]; ring)
  have h22 : M 2 2 ≠ 0 := fun h => hdet (by rw [hdet', h]; ring)
  refine ⟨Units.mk0 ν hν0, Units.mk0 (M 2 2) h22, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, e00, e01, e10, e11, h02, h12, h20, h21]

theorem graph_of_fix [Finite K] (h4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {A : GL (Fin 3) K}
    {τ : K ≃+* K}
    (h : ∀ B : SL(2, K), (conjAut 3 K A * fieldAut 3 K τ * dualAut 3 K)
      (proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) =
        proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) :
    τ = 1 ∧ ∃ μ : Kˣ, conjAut 3 K A = conjAut 3 K (sigMat μ) := by
  obtain ⟨-, -, -, hdd, -⟩ := standard_automorphism_transport (n := 3) (K := K)
  set S := sigMat (1 : Kˣ) with hSdef
  have hdinv : (dualAut 3 K)⁻¹ = dualAut 3 K := inv_eq_of_mul_eq_one_right hdd
  have hprod : conjAut 3 K A * fieldAut 3 K τ * dualAut 3 K * (conjAut 3 K S * dualAut 3 K)⁻¹ =
      conjAut 3 K (A * GeneralLinearGroup.map (τ : K →+* K) S⁻¹) * fieldAut 3 K τ := by
    rw [_root_.mul_inv_rev, hdinv, ← map_inv, map_mul, mul_assoc (conjAut 3 K A * fieldAut 3 K τ),
      ← mul_assoc (dualAut 3 K), hdd, one_mul, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  have hfix : ∀ B : SL(2, K), (conjAut 3 K (A * GeneralLinearGroup.map (τ : K →+* K) S⁻¹) *
      fieldAut 3 K τ) (proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B)) =
        proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B) := by
    intro B
    have h1 : (conjAut 3 K S * dualAut 3 K)⁻¹ (proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) =
        proj 3 K (blkP 1 (SpecialLinearGroup.toGL B)) :=
      (MulEquiv.symm_apply_eq _).2 (fix_sig_one B).symm
    show (conjAut 3 K (A * GeneralLinearGroup.map (τ : K →+* K) S⁻¹) * fieldAut 3 K τ)
      (proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) =
        proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))
    rw [← hprod, MulAut.mul_apply, h1]
    exact h B
  have hτ : τ = 1 := eq_one_of_fix h4 ((blkP 1).comp SpecialLinearGroup.toGL) (trace_blkP 1) hfix
  subst hτ
  refine ⟨rfl, ?_⟩
  have hmap : GeneralLinearGroup.map ((1 : K ≃+* K) : K →+* K) S⁻¹ = S⁻¹ :=
    Units.ext (by ext i j; rfl)
  have hfix' : ∀ B : SL(2, K),
      conjAut 3 K (A * S⁻¹) (proj 3 K (blkP 1 (SpecialLinearGroup.toGL B))) =
      proj 3 K (blkP 1 (SpecialLinearGroup.toGL B)) := by
    intro B
    have := hfix B
    rw [hmap, map_one, mul_one] at this
    exact this
  obtain ⟨ν, ν', hνν⟩ := eq_blk_scalar_of_fix h4 h2 hfix'
  refine ⟨ν / ν', ?_⟩
  have hA : A = GeneralLinearGroup.scalar (Fin 3) ν' * sigMat (ν / ν') := by
    apply Units.ext
    have e : (A : Matrix (Fin 3) (Fin 3) K) =
        ((A * S⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (S : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [e, hνν, hSdef, coe_sigMat, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_sigMat,
      Lemma41aL3.blkMat_mul]
    have hν' : (ν' : K) ≠ 0 := ν'.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, jMat] <;> field_simp
  rw [hA, map_mul, conjAut_scalar, one_mul]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
