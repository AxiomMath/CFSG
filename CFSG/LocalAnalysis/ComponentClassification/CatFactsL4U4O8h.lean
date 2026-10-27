module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)

variable {K : Type} [Field K] (c₀ : K)

theorem mulVec_single_apply {n : Type*} [Fintype n] [DecidableEq n] {R : Type*}
    [CommSemiring R] (M : Matrix n n R) (i j : n) (x : R) :
    (M *ᵥ Pi.single j x) i = M i j * x := by
  rw [Matrix.mulVec, dotProduct_single]

theorem trace_restrictScalars (M : Matrix (Fin 4) (Fin 4) (extension c₀)) :
    LinearMap.trace K (Fin 4 → extension c₀) ((Matrix.mulVecLin M).restrictScalars K) =
      2 * M.trace.re := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K
    (Pi.basis fun _ : Fin 4 => QuadraticAlgebra.basis c₀ (0 : K)), Matrix.trace,
    Fintype.sum_sigma]
  simp only [LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr,
    LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, mulVec_single_apply,
    QuadraticAlgebra.basis_repr_apply, Fin.sum_univ_two, QuadraticAlgebra.basis_apply_zero,
    QuadraticAlgebra.basis_apply_one, Matrix.diag_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, mul_zero, add_zero, zero_mul,
    Matrix.trace, Fin.sum_univ_four, QuadraticAlgebra.re_add, Matrix.diag_apply]
  ring

theorem re_omega_mul (z : extension c₀) :
    ((QuadraticAlgebra.omega : extension c₀) * z).re = c₀ * z.im := by
  simp [QuadraticAlgebra.re_mul]

theorem trace_restrictScalars_omega (M : Matrix (Fin 4) (Fin 4) (extension c₀)) :
    LinearMap.trace K (Fin 4 → extension c₀)
      ((Matrix.mulVecLin ((QuadraticAlgebra.omega : extension c₀) • M)).restrictScalars K) =
      2 * (c₀ * M.trace.im) := by
  rw [trace_restrictScalars, Matrix.trace_smul, smul_eq_mul, re_omega_mul]

theorem eq_of_eq_mul_scalar {d p : ℕ} [Fact p.Prime] [CharP K p] (hd : 0 < d)
    {X Y : GL (Fin d) K} (c : Kˣ) (hX : X ^ p = 1) (hY : Y ^ p = 1)
    (h : X = Y * GeneralLinearGroup.scalar (Fin d) c) : X = Y := by
  have hsc : GeneralLinearGroup.scalar (Fin d) c ∈ Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm : Commute Y (GeneralLinearGroup.scalar (Fin d) c) :=
    Subgroup.mem_center_iff.mp hsc Y
  have e2 : (Y * GeneralLinearGroup.scalar (Fin d) c) ^ p = 1 := by rw [← h, hX]
  rw [hcomm.mul_pow, hY, one_mul, ← map_pow] at e2
  have hc1 : c ^ p = 1 := by
    have := congrArg (fun Z : GL (Fin d) K => (Z : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩) e2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at this
    exact Units.val_eq_one.mp (by simpa using this)
  have hc2 : c = 1 := by
    have h3 : ((c : K) - 1) ^ p = 0 := by
      have e : (c : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hc1, Units.val_one]
      rw [sub_pow_char, e, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 h3))
  rw [h, hc2, map_one, mul_one]

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
