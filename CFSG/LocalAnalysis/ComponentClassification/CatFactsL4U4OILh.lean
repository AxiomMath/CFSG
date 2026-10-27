module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILg

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k]

theorem coord_g0 (δ : kˣ) (h2 : (2 : k) ≠ 0) (x : Fin 4 → k) :
    (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ (g0 (δ : k)) (hermitianCoordinates (δ : k) h2 x)) =
      ![x 1, x 0, -x 2, x 3] := by
  rw [hermitianCoordinates_symm_apply, rowOAction_val, hermitianCoordinates_val, coe_g0]
  funext i
  fin_cases i
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    QuadraticAlgebra.algebraMap_re]

@[expose] def qf (δ : k) (y : Fin 4 → k) : k := y 0 * y 1 - y 2 ^ 2 + δ * y 3 ^ 2

theorem hermitianForm_coord (δ : k) (h2 : (2 : k) ≠ 0) (y : Fin 4 → k) :
    hermitianForm δ (hermitianCoordinates δ h2 y) = qf δ y := by
  rw [hermitianForm_apply, hermitianCoordinates_val, qf]
  simp [QuadraticAlgebra.algebraMap_re]

@[expose] def mD (a b h : k) : Matrix (Fin 4) (Fin 4) k :=
  !![(1 + a) * h, (1 - a) * h, b, 0; (1 - a) * h, (1 + a) * h, -b, 0; b * h, -(b * h), -a, 0;
    0, 0, 0, 1]

theorem mD_mulVec (a b h : k) (w : Fin 4 → k) :
    mD a b h *ᵥ w = ![(1 + a) * h * w 0 + (1 - a) * h * w 1 + b * w 2,
      (1 - a) * h * w 0 + (1 + a) * h * w 1 - b * w 2, b * h * w 0 - b * h * w 1 - a * w 2,
      w 3] := by
  funext i
  fin_cases i
  all_goals simp [mD, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring

theorem det_mD {a b h : k} (hab : a ^ 2 + b ^ 2 = -1) (hh : 2 * h = 1) : (mD a b h).det = 1 := by
  simp [mD, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  linear_combination (-4 * h ^ 2) * hab + (2 * h + 1) * hh

theorem qf_polar_mD (δ : k) {a b h : k} (hab : a ^ 2 + b ^ 2 = -1) (hh : 2 * h = 1)
    (y z : Fin 4 → k) :
    qf δ (mD a b h *ᵥ y + mD a b h *ᵥ z) - qf δ (mD a b h *ᵥ y) - qf δ (mD a b h *ᵥ z) =
      qf δ (![y 1, y 0, -y 2, y 3] + z) - qf δ ![y 1, y 0, -y 2, y 3] - qf δ z := by
  simp only [qf, mD_mulVec, Pi.add_apply]
  simp
  linear_combination (2 * h + 1) * (y 0 * z 0 + y 1 * z 1) * hh -
    2 * (h ^ 2 * (y 0 - y 1) * (z 0 - z 1) + y 2 * z 2) * hab

theorem eq_of_dotProduct_mulVec {M N : Matrix (Fin 4) (Fin 4) k}
    (h : ∀ u v, u ⬝ᵥ (M *ᵥ v) = u ⬝ᵥ (N *ᵥ v)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem dotProduct_transpose_mul (A M : Matrix (Fin 4) (Fin 4) k) (u v : Fin 4 → k) :
    u ⬝ᵥ ((Aᵀ * M) *ᵥ v) = (A *ᵥ u) ⬝ᵥ (M *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem exists_isometry_g0 (δ : kˣ) (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k)) (R : GL (Fin 4) k)
    (hRT : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R)
    (hRf : ∀ v : Fin 4 → k,
      v ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = hermitianForm (δ : k) (ψ v))
    {a b : k} (hab : a ^ 2 + b ^ 2 = -1) :
    ∃ D : SpecialLinearGroup (Fin 4) k, (D : Matrix (Fin 4) (Fin 4) k)ᵀ * R * D =
      (rowOHom δ ψ (g0 (δ : k)) : Matrix (Fin 4) (Fin 4) k)ᵀ * R := by
  classical
  set hc := hermitianCoordinates (δ : k) h2 with hhc
  set e : (Fin 4 → k) ≃ₗ[k] (Fin 4 → k) := hc.trans ψ.symm with he
  have hh : 2 * (2 : k)⁻¹ = 1 := mul_inv_cancel₀ h2
  have hψe : ∀ v, ψ v = hc (e.symm v) := fun v => by
    change ψ v = hc (hc.symm (ψ v))
    rw [LinearEquiv.apply_symm_apply]
  have hQ : ∀ v, v ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = qf (δ : k) (e.symm v) :=
    fun v => by rw [hRf, hψe, hermitianForm_coord]
  have hsym : ∀ u v, v ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ u) =
      u ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ v) := fun u v => by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hRT]
  have hpol : ∀ u v, 2 * (u ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ v)) =
      qf (δ : k) (e.symm u + e.symm v) - qf (δ : k) (e.symm u) - qf (δ : k) (e.symm v) :=
    fun u v => by
      have h1 := hQ (u + v)
      rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hQ u, hQ v, hsym u v,
        map_add] at h1
      rw [← h1]
      ring
  set f : (Fin 4 → k) →ₗ[k] (Fin 4 → k) := e.conj (Matrix.toLin' (mD a b (2 : k)⁻¹)) with hf
  set D := LinearMap.toMatrix' f with hD
  have hDv : ∀ v, e.symm (D *ᵥ v) = mD a b (2 : k)⁻¹ *ᵥ e.symm v := fun v => by
    rw [hD, LinearMap.toMatrix'_mulVec, hf, LinearEquiv.conj_apply_apply, Matrix.toLin'_apply,
      LinearEquiv.symm_apply_apply]
  have hdet : D.det = 1 := by
    rw [hD, LinearMap.det_toMatrix', hf, LinearEquiv.conj_apply, LinearMap.comp_assoc,
      LinearMap.det_conj, LinearMap.det_toLin', det_mD hab hh]
  have hh0 : ∀ u, e.symm ((rowOHom δ ψ (g0 (δ : k)) : Matrix (Fin 4) (Fin 4) k) *ᵥ u) =
      ![e.symm u 1, e.symm u 0, -e.symm u 2, e.symm u 3] := fun u => by
    rw [show (rowOHom δ ψ (g0 (δ : k)) : Matrix (Fin 4) (Fin 4) k) *ᵥ u =
      ψ.symm (rowOAction δ (g0 (δ : k)) (ψ u)) from linearConjGL_mulVec ψ _ u]
    change hc.symm (ψ (ψ.symm _)) = _
    rw [LinearEquiv.apply_symm_apply, hψe, coord_g0]
  refine ⟨⟨D, hdet⟩, ?_⟩
  change Dᵀ * (R : Matrix (Fin 4) (Fin 4) k) * D = _
  apply eq_of_dotProduct_mulVec
  intro u v
  rw [Matrix.mul_assoc, dotProduct_transpose_mul, dotProduct_transpose_mul,
    ← Matrix.mulVec_mulVec]
  apply mul_left_cancel₀ h2
  rw [hpol, hpol, hDv, hDv, hh0, qf_polar_mD (δ : k) hab hh]

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
