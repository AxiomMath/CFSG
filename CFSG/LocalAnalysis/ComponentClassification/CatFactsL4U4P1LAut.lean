module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LTabs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native

theorem exists_aut_form (α : MulAut (projectiveSL 4 (ZMod 3))) :
    ∃ (A : GL (Fin 4) (ZMod 3)) (ε : ℕ), ε ≤ 1 ∧
      α = conjAut 4 (ZMod 3) A * dualAut 4 (ZMod 3) ^ ε := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (n := 4) (K := ZMod 3) (by norm_num)).2 α
  refine ⟨A, ε, hε, ?_⟩
  rw [Subsingleton.elim σ 1, map_one, mul_one]

theorem perm_induces (A : GL (Fin 4) (ZMod 3)) {ε : ℕ} (hε : ε ≤ 1)
    (g : projectiveSL 4 (ZMod 3)) :
    perm80 A * swap80 ^ ε * pi g * (perm80 A * swap80 ^ ε)⁻¹ =
      pi ((conjAut 4 (ZMod 3) A * dualAut 4 (ZMod 3) ^ ε) g) := by
  interval_cases ε
  · rw [pow_zero, pow_zero, mul_one, mul_one]
    exact perm80_conj_pi A g
  · rw [pow_one, pow_one, MulAut.mul_apply, ← perm80_conj_pi, ← swap80_conj_pi]
    group

theorem matD_mul_self : matN codeD * matN codeD = 1 := by decide +kernel

theorem matD_invT : matN codeD * (matN codeD)ᵀ = 1 := by decide +kernel

theorem invTab_D : invTab40 (ptTab (matN codeD)ᵀ) = ptTab (matN codeD) := by decide +kernel

theorem det_matD : (matN codeD).det = -1 := by decide +kernel

theorem matI_eq : matN codeI = 1 := by decide +kernel

theorem invTab_I : invTab40 (ptTab (matN codeI)ᵀ) = ptTab (matN codeI) := by decide +kernel

@[expose] def dGL : GL (Fin 4) (ZMod 3) := ⟨matN codeD, matN codeD, matD_mul_self, matD_mul_self⟩

theorem det_dGL : GeneralLinearGroup.det dGL = -1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_neg, Units.val_one]
  exact det_matD

theorem tp_uD : tp 80 uD = perm80 dGL := tp_tbl (rep_tab80 rfl matD_invT invTab_D)

theorem tp_uDS : tp 80 uDS = perm80 dGL * swap80 :=
  tp_tbl (rep_tab80_swap rfl matD_invT invTab_D)

theorem tp_uS : tp 80 uS = swap80 := by
  have h := tp_tbl (rep_tab80_swap (A := 1) (k := codeI) (k' := codeI)
    (by rw [Units.val_one, matI_eq]) (by rw [Units.val_one, matI_eq, Matrix.one_mul,
      Matrix.transpose_one]) invTab_I)
  rwa [map_one, one_mul] at h

theorem det_cases (A : GL (Fin 4) (ZMod 3)) :
    GeneralLinearGroup.det A = 1 ∨ GeneralLinearGroup.det A = -1 := by
  have h : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  rcases h _ (Units.ne_zero (GeneralLinearGroup.det A)) with h1 | h1
  · exact Or.inl (Units.val_eq_one.mp h1)
  · exact Or.inr (Units.val_eq_neg_one.mp h1)

theorem perm80_mem_range {A : GL (Fin 4) (ZMod 3)} (h : GeneralLinearGroup.det A = 1) :
    perm80 A ∈ pi.range := by
  have hdet : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, h, Units.val_one]
  let s : SpecialLinearGroup (Fin 4) (ZMod 3) := ⟨A, hdet⟩
  have hs : SpecialLinearGroup.toGL s = A := Units.ext (SpecialLinearGroup.coe_GL_coe_matrix s)
  refine MonoidHom.mem_range.mpr ⟨proj 4 (ZMod 3) s, ?_⟩
  rw [pi_proj, hs]

theorem det_mul_dGL_inv {A : GL (Fin 4) (ZMod 3)} (h : GeneralLinearGroup.det A = -1) :
    GeneralLinearGroup.det (A * dGL⁻¹) = 1 := by
  rw [map_mul, map_inv, h, det_dGL, mul_inv_cancel]

end CFSG.ComponentClassification.HarrisLit.P1.L43
