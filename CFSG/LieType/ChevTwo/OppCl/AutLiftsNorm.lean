module

public import CFSG.LieType.ChevTwo.OppCl.SLInduces

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section Norm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem exists_unit_sq_mul_eq_one [Finite F] [CharP F 2] (μ : Fˣ) :
    ∃ c : Fˣ, (c : F) * c * μ = 1 := by
  obtain ⟨d, hd⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) ((μ⁻¹ : Fˣ) : F)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (μ⁻¹).ne_zero (by rw [hd, mul_zero])
  refine ⟨Units.mk0 d hd0, ?_⟩
  rw [Units.val_mk0, ← hd, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem conj_matrix_scalar (c : Fˣ) (A : GL ι F) (M : Matrix ι ι F) :
    ((Matrix.GeneralLinearGroup.scalar ι c * A : GL ι F) : Matrix ι ι F) * M *
        (((Matrix.GeneralLinearGroup.scalar ι c * A)⁻¹ : GL ι F) : Matrix ι ι F) =
      (A : Matrix ι ι F) * M * ((A⁻¹ : GL ι F) : Matrix ι ι F) := by
  have hc : ∀ N : Matrix ι ι F, ((Matrix.GeneralLinearGroup.scalar ι c : GL ι F) :
      Matrix ι ι F) * N = N * (Matrix.GeneralLinearGroup.scalar ι c : GL ι F) := by
    intro N
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) N).eq
  rw [mul_inv_rev]
  simp only [Units.val_mul]
  calc ((Matrix.GeneralLinearGroup.scalar ι c : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) * M *
        (((A⁻¹ : GL ι F) : Matrix ι ι F) *
          (((Matrix.GeneralLinearGroup.scalar ι c)⁻¹ : GL ι F) : Matrix ι ι F))
      = ((Matrix.GeneralLinearGroup.scalar ι c : GL ι F) : Matrix ι ι F) *
          ((A : Matrix ι ι F) * M * ((A⁻¹ : GL ι F) : Matrix ι ι F)) *
          (((Matrix.GeneralLinearGroup.scalar ι c)⁻¹ : GL ι F) : Matrix ι ι F) := by
        simp only [Matrix.mul_assoc]
    _ = (A : Matrix ι ι F) * M * ((A⁻¹ : GL ι F) : Matrix ι ι F) := by
        rw [hc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]

theorem semilinMap_scalar_mul (c : Fˣ) (A : GL ι F) (σ : F ≃+* F) (v : ι → F) :
    semilinMap (Matrix.GeneralLinearGroup.scalar ι c * A) σ v = (c : F) • semilinMap A σ v := by
  rw [semilinMap_apply, semilinMap_apply, Units.val_mul, ← Matrix.mulVec_mulVec,
    Matrix.GeneralLinearGroup.coe_scalar]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

variable [Finite F]

theorem induces_of_conj_scalar (H : Subgroup (GL ι F)) (A : GL ι F) (c : Fˣ) (σ : F ≃+* F)
    (α : MulAut (StatedProj H))
    (hα : ∀ h : H, ∃ h' : H, ((h' : GL ι F) : Matrix ι ι F) =
        (A : Matrix ι ι F) * ((h : GL ι F) : Matrix ι ι F).map σ * ((A⁻¹ : GL ι F) : Matrix ι ι F) ∧
      α (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H) h) =
        QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H) h') :
    Induces (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) (natRep H)
      (semilinMap (Matrix.GeneralLinearGroup.scalar ι c * A) σ) α :=
  induces_of_conj H _ σ α fun h => by
    obtain ⟨h', h1, h2⟩ := hα h
    exact ⟨h', by rw [h1, conj_matrix_scalar], h2⟩

end Norm

end CFSG.LieType.ChevTwo.OppCl
