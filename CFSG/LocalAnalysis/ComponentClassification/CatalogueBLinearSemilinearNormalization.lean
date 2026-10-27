module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearAction

public section

namespace CFSG.ComponentClassification.CatalogueBLinearSemilinear

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField

universe u

theorem cocycle_scalar_fixed (n : ℕ) {K : Type u} [Field K]
    (hn : 1 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c = A * glFieldAut (Fin n) K sigma A) :
    sigma (c : K) = c := by
  have hdouble : glFieldAut (Fin n) K sigma (glFieldAut (Fin n) K sigma A) = A := by
    have h := DFunLike.congr_fun (congrArg (glFieldAut (Fin n) K) hsigma) A
    simpa [map_pow, pow_two] using h
  have hreverse : glFieldAut (Fin n) K sigma A * A = GeneralLinearGroup.scalar (Fin n) c := by
    calc
      glFieldAut (Fin n) K sigma A * A =
          A⁻¹ * (A * glFieldAut (Fin n) K sigma A) * A := by group
      _ = A⁻¹ * GeneralLinearGroup.scalar (Fin n) c * A := by rw [← hc]
      _ = GeneralLinearGroup.scalar (Fin n) c := by
        rw [mul_assoc, GeneralLinearGroup.scalar_commute]
        group
  have hmapped : glFieldAut (Fin n) K sigma A * A =
      GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom c) := by
    calc
      glFieldAut (Fin n) K sigma A * A =
          glFieldAut (Fin n) K sigma (A * glFieldAut (Fin n) K sigma A) := by
        rw [map_mul, hdouble]
      _ = glFieldAut (Fin n) K sigma (GeneralLinearGroup.scalar (Fin n) c) := by rw [← hc]
      _ = GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom c) :=
        glFieldEquiv_scalar (Fin n) sigma c
  let i : Fin n := ⟨0, by omega⟩
  have hentry := congrArg (fun M : GL (Fin n) K => M i i) (hmapped.symm.trans hreverse)
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hentry

theorem exists_normalized_cocycle (n : ℕ) {K : Type u} [Field K] [Finite K]
    (hn : 1 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c = A * glFieldAut (Fin n) K sigma A) :
    ∃ b : Kˣ,
      (GeneralLinearGroup.scalar (Fin n) b * A) *
          glFieldAut (Fin n) K sigma (GeneralLinearGroup.scalar (Fin n) b * A) = 1 ∧
        semilinearAction n K (GeneralLinearGroup.scalar (Fin n) b * A) sigma =
          semilinearAction n K A sigma := by
  have hfixed : sigma (c⁻¹ : Kˣ) = (c⁻¹ : Kˣ) := by
    simp only [Units.val_inv_eq_inv_val, map_inv₀,
      cocycle_scalar_fixed n hn A sigma hsigma c hc]
  obtain ⟨b, hb⟩ := CatalogueBLinearTwoDescent.exists_norm_unit K sigma hsigma hne c⁻¹ hfixed
  have hunit : b * Units.map sigma.toMonoidHom b * c = 1 := by
    apply Units.ext
    change (b : K) * sigma (b : K) * (c : K) = 1
    rw [hb, Units.val_inv_eq_inv_val]
    exact inv_mul_cancel₀ (Units.ne_zero c)
  refine ⟨b, ?_, ?_⟩
  · have hscalar : glFieldAut (Fin n) K sigma (GeneralLinearGroup.scalar (Fin n) b) =
        GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b) :=
      glFieldEquiv_scalar (Fin n) sigma b
    rw [map_mul, hscalar]
    calc
      (GeneralLinearGroup.scalar (Fin n) b * A) *
          (GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b) *
            glFieldAut (Fin n) K sigma A) =
          (GeneralLinearGroup.scalar (Fin n) b *
            GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b)) *
              (A * glFieldAut (Fin n) K sigma A) := by
        rw [mul_assoc (GeneralLinearGroup.scalar (Fin n) b) A,
          ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
        group
      _ = (GeneralLinearGroup.scalar (Fin n) b *
            GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b)) *
              GeneralLinearGroup.scalar (Fin n) c := by rw [← hc]
      _ = 1 := by rw [← map_mul, ← map_mul, hunit, map_one]
  · simp [semilinearAction, map_mul, innerDiagonalAction_scalar]

end

end CFSG.ComponentClassification.CatalogueBLinearSemilinear
