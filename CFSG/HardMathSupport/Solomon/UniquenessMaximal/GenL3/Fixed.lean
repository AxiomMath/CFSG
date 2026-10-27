module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLDescent

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open Matrix CFSG.Quasithin.SteinbergCB.GDescent CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.HardMathSupport.Solomon.Coordinator

variable {F : Type} [Field F] [Finite F]

theorem hilbert90_three {σ : F ≃+* F} (hσ : orderOf σ = 3) {c : F} (hc0 : c ≠ 0)
    (hN : c * σ c * σ (σ c) = 1) : ∃ μ : F, μ ≠ 0 ∧ c * σ μ = μ := by
  set B : Matrix (Fin 1) (Fin 1) F := Matrix.of fun _ _ => c with hB
  have hBu : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : B.det = c := by simp [hB, Matrix.det_unique]
    rw [this]
    exact isUnit_iff_ne_zero.2 hc0
  have hC : iterMat σ B 3 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [iterMat, hB, Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply]
    linear_combination hN
  obtain ⟨P, hPu, hP⟩ := bgll_exists_fixed_basis σ hσ (by norm_num) hBu hC
  have hP0 : P 0 0 ≠ 0 := by
    intro h
    have hdet : P.det = P 0 0 := by simp [Matrix.det_unique]
    exact ((Matrix.isUnit_iff_isUnit_det P).1 hPu).ne_zero (by rw [hdet, h])
  refine ⟨P 0 0, hP0, ?_⟩
  have := congrFun (congrFun hP 0) 0
  simpa [hB, Matrix.mul_apply, Matrix.map_apply] using this

theorem exists_scalar_fixed {σ : F ≃+* F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hcomm : conjAut 3 F g * fieldAut 3 F σ = fieldAut 3 F σ * conjAut 3 F g) :
    ∃ μ : F, μ ≠ 0 ∧ ∀ i j, σ (μ * (g : Matrix (Fin 3) (Fin 3) F) i j) =
      μ * (g : Matrix (Fin 3) (Fin 3) F) i j := by
  have e1 : fieldAut 3 F σ * conjAut 3 F g =
      conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) g) * fieldAut 3 F σ := by
    have := conjAut_mul_fieldAut_mul (n := 3) (K := F) 1 g σ 1
    simpa using this
  have e2 : conjAut 3 F g = conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) g) :=
    mul_right_cancel (hcomm.trans e1)
  have hs : conjAut 3 F (g⁻¹ * GeneralLinearGroup.map (σ : F →+* F) g) * fieldAut 3 F 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, ← e2, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ 1 hs
  have hmapg : GeneralLinearGroup.map (σ : F →+* F) g = g * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc]; group
  have hGσ : (g : Matrix (Fin 3) (Fin 3) F).map σ = (c : F) • (g : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hmapg
    simp only [bgll_coe_mul_scalar] at this
    exact this
  have hGu : IsUnit (g : Matrix (Fin 3) (Fin 3) F) := g.isUnit
  have hG0 : (g : Matrix (Fin 3) (Fin 3) F) ≠ 0 := hGu.ne_zero
  have hmap : ∀ (a : F) (M : Matrix (Fin 3) (Fin 3) F), (a • M).map σ = σ a • M.map σ :=
    fun a M => smul_map σ a M
  have hN : (c : F) * σ c * σ (σ c) = 1 := by
    have h1 := bgll_map_cube hσ (g : Matrix (Fin 3) (Fin 3) F)
    simp only [hGσ, hmap, smul_smul, map_mul] at h1
    have h2 : (σ (σ c) * σ c * c - 1) • (g : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · linear_combination h
    · exact absurd h hG0
  obtain ⟨μ, hμ0, hμ⟩ := hilbert90_three hσ c.ne_zero hN
  refine ⟨μ, hμ0, fun i j => ?_⟩
  have h1 := congrFun (congrFun hGσ i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
  rw [map_mul, h1]
  linear_combination ((g : Matrix (Fin 3) (Fin 3) F) i j) * hμ

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
