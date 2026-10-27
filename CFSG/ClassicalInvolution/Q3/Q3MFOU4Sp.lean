module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Conj
public import CFSG.ClassicalInvolution.Asc77.AscCX9X2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77.CX.MF2L CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

structure GraphData : Type where
  ι : F9
  ζ : F9
  m : F9
  n : F9
  hι : ι * ι = -1
  hιb : σ9 ι = -ι
  hζ : σ9 ζ * ζ = -1
  hm : σ9 m * m = 1
  hn : σ9 n * n = 1

namespace GraphData

variable (D : GraphData)

theorem ι_ne_zero : D.ι ≠ 0 := by
  intro h
  have := D.hι
  rw [h] at this
  simp at this

theorem ζ_ne_zero : D.ζ ≠ 0 := by
  intro h
  have := D.hζ
  rw [h, map_zero] at this
  simp at this

theorem m_ne_zero : D.m ≠ 0 := by
  intro h
  have := D.hm
  rw [h, map_zero] at this
  simp at this

theorem n_ne_zero : D.n ≠ 0 := by
  intro h
  have := D.hn
  rw [h, map_zero] at this
  simp at this

@[expose] noncomputable def M : Matrix (Fin 4) (Fin 4) F9 := Mmat D.ζ D.ι D.m D.n

@[expose] noncomputable def G : Matrix (Fin 4) (Fin 4) F9 := Gmat D.m D.n

theorem det_M_ne_zero : D.M.det ≠ 0 :=
  det_Mmat_ne_zero two_ne_zero_F9 D.ζ_ne_zero D.ι_ne_zero D.m_ne_zero D.n_ne_zero

@[expose] noncomputable def Mg : GL (Fin 4) F9 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero D.M D.det_M_ne_zero

noncomputable def Mi : Matrix (Fin 4) (Fin 4) F9 := ((D.Mg⁻¹ : GL (Fin 4) F9) : Matrix _ _ F9)

theorem coe_Mg : ((D.Mg : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = D.M := rfl

theorem M_mul_Mi : D.M * D.Mi = 1 := by
  rw [Mi, ← coe_Mg, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem Mi_mul_M : D.Mi * D.M = 1 := by
  rw [Mi, ← coe_Mg, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem gram_M : (D.M.map σ9)ᵀ * D.M = D.ι • (Omg F9) :=
  gram_Mmat σ9 D.hιb D.hζ D.hm D.hn three_eq_zero_F9

theorem twist_M : D.ζ • (D.G * D.M.map σ9) = D.M :=
  twist_Mmat σ9 D.hιb D.hζ D.hm D.hn three_eq_zero_F9

end GraphData

section Psi

theorem hm1 : (-1 : F3) ≠ 0 := neg_ne_zero.mpr one_ne_zero

noncomputable abbrev kap : StatedSp 2 F3 →* SL(4, F3) := kappa (F := F3) hm1 hm1

theorem spForm_neg_one : spForm (-1 : F3) (-1) = Omg F3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm, Omg]

theorem Omg_map : (Omg F3).map embF = Omg F9 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Omg]

noncomputable def Yq (x : StatedSp 2 F3) : Matrix (Fin 4) (Fin 4) F9 :=
  ((kap x : SL(4, F3)) : Matrix (Fin 4) (Fin 4) F3).map embF

theorem Yq_map (x : StatedSp 2 F3) : (Yq x).map σ9 = Yq x := by
  ext i j
  simp only [Yq, Matrix.map_apply]
  exact σ9_embF _

theorem Yq_det (x : StatedSp 2 F3) : (Yq x).det = 1 := by
  have h : ((kap x : SL(4, F3)) : Matrix (Fin 4) (Fin 4) F3).det = 1 := (kap x).2
  have h2 : (Yq x).det = embF (((kap x : SL(4, F3)) : Matrix (Fin 4) (Fin 4) F3).det) := by
    rw [Yq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h2, h, map_one]

theorem Yq_gram (x : StatedSp 2 F3) : (Yq x)ᵀ * Omg F9 * Yq x = Omg F9 := by
  have h1 := mem_spM.mp (kappa_mem_spM hm1 hm1 x)
  rw [spForm_neg_one] at h1
  have h2 := symp_transpose _ h1
  have h3 := congrArg (fun A => Matrix.map A embF) h2
  simpa [Yq, Matrix.map_mul, Matrix.transpose_map, Omg_map] using h3

namespace GraphData

variable (D : GraphData)

noncomputable def psiGL : StatedSp 2 F3 →* GL (Fin 4) F9 :=
  (MulAut.conj D.Mg).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map embF).comp (Matrix.SpecialLinearGroup.toGL.comp kap))

theorem coe_psiGL (x : StatedSp 2 F3) :
    ((D.psiGL x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = D.M * Yq x * D.Mi := by
  simp only [psiGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Units.val_mul]
  rfl

theorem psiGL_mem (x : StatedSp 2 F3) : D.psiGL x ∈ SUid σ9 4 := by
  rw [mem_SUid]
  refine ⟨?_, ?_⟩
  · rw [coe_psiGL]
    have := Matrix.det_units_conj D.Mg (Yq x)
    rw [coe_Mg] at this
    rw [show D.Mi = ((D.Mg⁻¹ : GL (Fin 4) F9) : Matrix _ _ F9) from rfl]
    rw [this, Yq_det]
  · rw [coe_psiGL]
    show ((D.M * Yq x * D.Mi).map σ9)ᵀ * (D.M * Yq x * D.Mi) = 1
    exact unitary_conj_of_gram σ9 D.M_mul_Mi D.gram_M (by rw [Yq_map]; exact Yq_gram x)

noncomputable def psi : StatedSp 2 F3 →* Su F9 3 1 4 :=
  D.psiGL.codRestrict (SUid σ9 4) D.psiGL_mem

theorem suMat_psi (x : StatedSp 2 F3) : suMat (D.psi x) = D.M * Yq x * D.Mi := coe_psiGL D x

theorem psi_comm (x : StatedSp 2 F3) :
    D.G * (suMat (D.psi x)).map σ9 = suMat (D.psi x) * D.G := by
  rw [suMat_psi]
  exact comm_conj_of_map_eq σ9 D.ζ_ne_zero D.M_mul_Mi D.Mi_mul_M D.twist_M (Yq_map x)

theorem psi_range (x : Su F9 3 1 4) (hx : D.G * (suMat x).map σ9 = suMat x * D.G) :
    ∃ y : StatedSp 2 F3, D.psi y = x := by
  set X := suMat x with hX
  set Y : Matrix (Fin 4) (Fin 4) F9 := D.Mi * X * D.M with hY
  have hYσ : Y.map σ9 = Y := map_conj_eq_of_comm σ9 D.M_mul_Mi D.Mi_mul_M D.twist_M hx
  have hYdet : Y.det = 1 := by
    have h1 : Y.det = X.det := Matrix.det_units_conj' D.Mg X
    rw [h1]
    exact det_suMat x
  have hXu : (X.map σ9)ᵀ * X = 1 := (mem_SUid.mp x.2).2
  have hgr := gram_conj_of_unitary σ9 D.M_mul_Mi hXu hY
  rw [D.gram_M, hYσ] at hgr
  have hYg : Yᵀ * Omg F9 * Y = Omg F9 := by
    have h1 : D.ι • (Yᵀ * Omg F9 * Y) = D.ι • Omg F9 := by
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using hgr
    exact smul_right_injective _ D.ι_ne_zero h1
  have hent : ∀ i j, ∃ c : F3, embF c = Y i j := fun i j => by
    refine exists_embF ?_
    have h1 := congrFun (congrFun hYσ i) j
    rwa [Matrix.map_apply] at h1
  choose y0 hy0 using hent
  obtain ⟨y, hYy⟩ : ∃ y : Matrix (Fin 4) (Fin 4) F3, Y = y.map embF :=
    ⟨Matrix.of y0, by ext i j; exact (hy0 i j).symm⟩
  have hdy : y.det = 1 := by
    apply embF_injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, ← hYy]
    exact hYdet
  have hyg : yᵀ * Omg F3 * y = Omg F3 := by
    refine Matrix.map_injective embF_injective ?_
    show (yᵀ * Omg F3 * y).map embF = (Omg F3).map embF
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Omg_map, ← hYy]
    exact hYg
  have hyg' : y * Omg F3 * yᵀ = Omg F3 := by
    have := symp_transpose yᵀ (by rw [Matrix.transpose_transpose]; exact hyg)
    rwa [Matrix.transpose_transpose] at this
  obtain ⟨sl, hsl⟩ : ∃ sl : SL(4, F3), (sl : Matrix (Fin 4) (Fin 4) F3) = y := ⟨⟨y, hdy⟩, rfl⟩
  have hmem : sl ∈ spM (spForm (-1 : F3) (-1)) := by
    rw [mem_spM, spForm_neg_one, hsl]
    exact hyg'
  rw [← kappa_range hm1 hm1] at hmem
  obtain ⟨xs, hxs⟩ := hmem
  refine ⟨xs, suMat_injective ?_⟩
  have hYq : Yq xs = Y := by
    have h1 : ((kap xs : SL(4, F3)) : Matrix (Fin 4) (Fin 4) F3) = y := by
      rw [← hsl]
      exact congrArg (fun z : SL(4, F3) => (z : Matrix (Fin 4) (Fin 4) F3)) hxs
    rw [Yq, h1, hYy]
  rw [suMat_psi, hYq, hY]
  calc D.M * (D.Mi * X * D.M) * D.Mi = (D.M * D.Mi) * X * (D.M * D.Mi) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [D.M_mul_Mi, Matrix.one_mul, Matrix.mul_one]

theorem psi_ker (x : StatedSp 2 F3) (hx : D.psi x ∈ Subgroup.center (Su F9 3 1 4)) :
    x ∈ Subgroup.center (StatedSp 2 F3) := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center isUnitaryInvolution_σ9 (by norm_num : 3 ≤ 4) hx
  have hsu : D.M * Yq x * D.Mi = Matrix.scalar (Fin 4) (u : F9) := by
    rw [← suMat_psi]
    exact hu
  have hYx : Yq x = Matrix.scalar (Fin 4) (u : F9) := by
    calc Yq x = (D.Mi * D.M) * Yq x * (D.Mi * D.M) := by
          rw [D.Mi_mul_M, Matrix.one_mul, Matrix.mul_one]
      _ = D.Mi * (D.M * Yq x * D.Mi) * D.M := by simp only [Matrix.mul_assoc]
      _ = Matrix.scalar (Fin 4) (u : F9) := by
          rw [hsu, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
            Matrix.mul_one, Matrix.smul_mul, D.Mi_mul_M]
  set a : Matrix (Fin 4) (Fin 4) F3 := ((kap x : SL(4, F3)) : Matrix (Fin 4) (Fin 4) F3) with ha
  have hentry : ∀ i j, embF (a i j) = if i = j then (u : F9) else 0 := by
    intro i j
    have h1 := congrFun (congrFun hYx i) j
    simp only [Yq, Matrix.map_apply] at h1
    rw [h1, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hscal : a = (a 0 0) • (1 : Matrix (Fin 4) (Fin 4) F3) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have h1 : embF (a i i) = embF (a 0 0) := by rw [hentry i i, hentry 0 0]; simp
      have h2 : a i i = a 0 0 := embF_injective h1
      simpa [Matrix.smul_apply] using h2
    · have h1 : embF (a i j) = embF 0 := by rw [hentry i j, map_zero]; simp [hij]
      have h2 : a i j = 0 := embF_injective h1
      simp [Matrix.one_apply_ne hij, h2]
  have hdet : (a 0 0) ^ 4 = 1 := by
    have h1 : a.det = 1 := (kap x).2
    rw [hscal, Matrix.det_smul, Matrix.det_one] at h1
    simpa using h1
  have hc : kap x ∈ Subgroup.center SL(4, F3) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    exact ⟨a 0 0, by simpa using hdet, by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
      exact hscal.symm⟩
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply kappa_injective hm1 hm1
  rw [map_mul, map_mul]
  exact hc (kap y)

end GraphData

end Psi

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
