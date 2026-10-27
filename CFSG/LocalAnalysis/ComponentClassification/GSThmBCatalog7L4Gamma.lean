module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Six

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open CFSG.ComponentClassification.Burgoyne.PSL (graphLift toGL_graphLift conjAut_mul_dualAut_proj)

variable {k : Type} [Field k]

theorem sl_ext {n : ℕ} {A B : SpecialLinearGroup (Fin n) k}
    (h : (A : Matrix (Fin n) (Fin n) k) = (B : Matrix (Fin n) (Fin n) k)) : A = B :=
  Subtype.ext h

theorem det_jj : (jj : Matrix (Fin 2) (Fin 2) k).det = 1 := by
  simp [jj, Matrix.det_fin_two]

theorem jj_mul_jj : (jj : Matrix (Fin 2) (Fin 2) k) * jj = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two]

theorem jj_mul_inv_transpose (U : SpecialLinearGroup (Fin 2) k) :
    jj * ((U⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ =
      (U : Matrix (Fin 2) (Fin 2) k) * jj := by
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def gramM (d : k) : Matrix (Fin 4) (Fin 4) k := bd (d • jj) jj

theorem det_gramM (d : k) : (gramM d).det = d ^ 2 := by
  rw [gramM, det_bd, det_smul, Fintype.card_fin, det_jj, mul_one, mul_one]

@[expose] def gramGL {d : k} (hd : d ≠ 0) : GL (Fin 4) k :=
  GeneralLinearGroup.mkOfDetNeZero (gramM d) (by rw [det_gramM]; exact pow_ne_zero 2 hd)

theorem coe_gramGL {d : k} (hd : d ≠ 0) :
    ((gramGL hd : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) = gramM d := rfl

theorem coe_gramGL_inv {d : k} (hd : d ≠ 0) :
    (((gramGL hd)⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) = bd (-(d⁻¹) • jj) (-jj) := by
  have hA : (d • jj : Matrix (Fin 2) (Fin 2) k) * (-(d⁻¹) • jj) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hB : (jj : Matrix (Fin 2) (Fin 2) k) * -jj = 1 := by
    rw [mul_neg, jj_mul_jj, neg_neg]
  have h : gramM d * bd (-(d⁻¹) • jj) (-jj) = 1 := by
    rw [gramM, bd_mul, hA, hB, bd_one]
  have hdet : (bd (-(d⁻¹) • jj) (-jj) : Matrix (Fin 4) (Fin 4) k).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  have hu : (gramGL hd)⁻¹ = GeneralLinearGroup.mkOfDetNeZero _ hdet := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    exact h
  rw [hu]
  rfl

theorem graph_gram_apply {d : k} (hd : d ≠ 0) {X Y : SpecialLinearGroup (Fin 4) k}
    (h : (Y : Matrix (Fin 4) (Fin 4) k) * gramM d =
      gramM d * ((X⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)ᵀ) :
    graphLift (gramGL hd) X = Y := by
  apply sl_ext
  have e := graphLift_mul (gramGL hd) X
  rw [coe_gramGL, ← h] at e
  have hinv := Units.mul_inv (gramGL hd)
  rw [coe_gramGL] at hinv
  calc ((graphLift (gramGL hd) X : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
      = (graphLift (gramGL hd) X : SpecialLinearGroup (Fin 4) k) * gramM d *
          (((gramGL hd)⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = (Y : Matrix (Fin 4) (Fin 4) k) * gramM d *
          (((gramGL hd)⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) := by rw [e]
    _ = Y := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem graph_gram_fixes_bdL {d : k} (hd : d ≠ 0) (U : SpecialLinearGroup (Fin 2) k) :
    (conjAut 4 k (gramGL hd) * dualAut 4 k) (proj 4 k (bdL k U)) = proj 4 k (bdL k U) := by
  rw [conjAut_mul_dualAut_proj, graph_gram_apply hd]
  rw [← map_inv, coe_bdL, coe_bdL, transpose_bd, transpose_one, gramM, bd_mul, bd_mul, one_mul,
    mul_one, Matrix.mul_smul, Matrix.smul_mul, jj_mul_inv_transpose]

theorem graph_gram_fixes_bdR {d : k} (hd : d ≠ 0) (W : SpecialLinearGroup (Fin 2) k) :
    (conjAut 4 k (gramGL hd) * dualAut 4 k) (proj 4 k (bdR k W)) = proj 4 k (bdR k W) := by
  rw [conjAut_mul_dualAut_proj, graph_gram_apply hd]
  rw [← map_inv, coe_bdR, coe_bdR, transpose_bd, transpose_one, gramM, bd_mul, bd_mul, one_mul,
    mul_one, jj_mul_inv_transpose]

theorem X1_mul_X1 (l m : k) : X1 l * X1 m = bd ((l * m) • 1) ((l * m) • 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, bd, Matrix.mul_apply, Fin.sum_univ_four]

theorem graph_gram_fixes_X1 {d : k} (hd : d ≠ 0) {b : k} (hb : b ≠ 0) (hb4 : b ^ 4 = 1)
    {g : SpecialLinearGroup (Fin 4) k} (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) :
    (conjAut 4 k (gramGL hd) * dualAut 4 k) (proj 4 k g) = proj 4 k g := by
  have hginv : ((g⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) = X1 b⁻¹ := by
    have h1 : X1 b⁻¹ * X1 b = 1 := by
      rw [X1_mul_X1, inv_mul_cancel₀ hb, one_smul, bd_one]
    calc ((g⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
        = X1 b⁻¹ * ((g : Matrix (Fin 4) (Fin 4) k) *
            ((g⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)) := by
          rw [← Matrix.mul_assoc, hg, h1, Matrix.one_mul]
      _ = X1 b⁻¹ := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have hdet : (X1 b⁻¹).det = 1 := by
    rw [← hginv]
    exact (g⁻¹).2
  set Y : SpecialLinearGroup (Fin 4) k := ⟨X1 b⁻¹, hdet⟩ with hY
  have hXT : (X1 b⁻¹)ᵀ = X1 b⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X1]
  rw [conjAut_mul_dualAut_proj, graph_gram_apply hd (Y := Y)]
  · symm
    rw [proj_eq_proj_iff, mem_scalars]
    refine ⟨(Units.mk0 b hb)⁻¹ ^ 2, ?_, ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_mk0, Units.val_one, ← pow_mul, inv_pow,
        show b ^ (2 * 4) = (b ^ 4) ^ 2 by ring, hb4, one_pow, inv_one]
    · rw [Matrix.SpecialLinearGroup.coe_mul, hginv]
      change X1 b⁻¹ * X1 b⁻¹ = _
      rw [X1_mul_X1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [bd, Matrix.scalar_apply, pow_two]
  · change X1 b⁻¹ * gramM d = gramM d * _
    rw [hginv, hXT, gramM, bd_comm_X1]

theorem conjAut_scalar_eq_one (c : kˣ) : conjAut 4 k (GeneralLinearGroup.scalar (Fin 4) c) = 1 := by
  unfold LinearFlag.conjAut
  rw [MonoidHom.comp_apply, CatalogueBHigherLinearAction.slConjugation_scalar, map_one]

theorem dualAut_mul_conjAut (A : GL (Fin 4) k) :
    dualAut 4 k * conjAut 4 k A =
      conjAut 4 k (GeneralLinearGroup.inverseTranspose A) * dualAut 4 k := by
  rw [← OddSelector.dualAut_conj_conjAut, OddSelector.dualAut_inv, mul_assoc, mul_assoc,
    (standard_automorphism_transport (K := k) (n := 4)).2.2.2.1, mul_one]

theorem graph_gram_sq {d : k} (hd : d ≠ 0) :
    (conjAut 4 k (gramGL hd) * dualAut 4 k) ^ 2 = 1 := by
  have hM : gramGL hd * GeneralLinearGroup.inverseTranspose (gramGL hd) =
      GeneralLinearGroup.scalar (Fin 4) (-1) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, coe_gramGL_inv, coe_gramGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gramM, bd, jj, Matrix.mul_apply, Fin.sum_univ_four, Matrix.scalar_apply, hd]
  rw [pow_two, mul_assoc, ← mul_assoc (dualAut 4 k), dualAut_mul_conjAut, mul_assoc,
    (standard_automorphism_transport (K := k) (n := 4)).2.2.2.1, mul_one,
    (standard_automorphism_transport (K := k) (n := 4)).1, hM, conjAut_scalar_eq_one]

theorem graph_gram_mem_coset {d : k} (hd : d ≠ 0) {B : GL (Fin 4) k}
    (hB : (B : Matrix (Fin 4) (Fin 4) k).det = d ^ 2) :
    (conjAut 4 k B * dualAut 4 k)⁻¹ * (conjAut 4 k (gramGL hd) * dualAut 4 k) ∈
      OuterAutomorphisms.inner (projectiveSL 4 k) := by
  have e : (conjAut 4 k B * dualAut 4 k)⁻¹ * (conjAut 4 k (gramGL hd) * dualAut 4 k) =
      conjAut 4 k (GeneralLinearGroup.inverseTranspose (B⁻¹ * gramGL hd)) := by
    rw [_root_.mul_inv_rev, OddSelector.dualAut_inv, ← map_inv, ← OddSelector.dualAut_conj_conjAut,
      OddSelector.dualAut_inv, map_mul]
    group
  rw [e]
  refine OddSelector.conjAut_mem_inner (c := 1) ?_
  apply Units.ext
  rw [one_pow, Units.val_one, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.coe_inverseTranspose, det_transpose, _root_.mul_inv_rev, inv_inv,
    Units.val_mul, det_mul, hB]
  have h1 := congrArg Matrix.det (Units.inv_mul (gramGL hd))
  rw [det_mul, det_one, coe_gramGL, det_gramM] at h1
  exact h1

theorem det_antiblock {B : Matrix (Fin 4) (Fin 4) k} (h00 : B 0 0 = 0) (h01 : B 0 1 = 0)
    (h10 : B 1 0 = 0) (h11 : B 1 1 = 0) (h22 : B 2 2 = 0) (h23 : B 2 3 = 0) (h32 : B 3 2 = 0)
    (h33 : B 3 3 = 0) :
    B.det = (B 0 2 * B 1 3 - B 0 3 * B 1 2) * (B 2 0 * B 3 1 - B 2 1 * B 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, h00, h01,
    h10, h11, h22, h23, h32, h33]
  ring

theorem antiblock_det_eq {B : Matrix (Fin 4) (Fin 4) k} (hB : Bᵀ = B ∨ Bᵀ = -B) :
    B 2 0 * B 3 1 - B 2 1 * B 3 0 = B 0 2 * B 1 3 - B 0 3 * B 1 2 := by
  rcases hB with h | h
  · have e : ∀ i j, B j i = B i j := fun i j => by
      have := congrFun (congrFun h i) j
      rwa [Matrix.transpose_apply] at this
    rw [e 0 2, e 1 3, e 1 2, e 0 3]
    ring
  · have e : ∀ i j, B j i = -B i j := fun i j => by
      have := congrFun (congrFun h i) j
      rwa [Matrix.transpose_apply, Matrix.neg_apply] at this
    rw [e 0 2, e 1 3, e 1 2, e 0 3]
    ring

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
