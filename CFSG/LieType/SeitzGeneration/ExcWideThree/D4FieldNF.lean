module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

section NormalForm


variable {K : Type} [Field K]

theorem rootDiagAut_eq_normalAut (a : Fin Tag.D4.rank → Kˣ) :
    rootDiagAut Tag.D4 K a = exactNormalAut Tag.D4 K a 1 0 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_rootDiagAut, coe_exactNormalAut, exactQ_D4]
  simp only [inv_one, mul_one, one_mul]
  congr 2
  exact (Units.ext (entrywise_id _)).symm

theorem normalForm_mul (g₁ g₂ : adjointGroup Tag.D4 K) (a₁ a₂ : Fin Tag.D4.rank → Kˣ)
    (σ₁ σ₂ : K ≃+* K) (ε : ℕ) :
    ∃ (g₃ : adjointGroup Tag.D4 K) (a₃ : Fin Tag.D4.rank → Kˣ),
      (MulAut.conj g₁ * exactNormalAut Tag.D4 K a₁ σ₁ 0) *
          (MulAut.conj g₂ * (exactNormalAut Tag.D4 K a₂ σ₂ 0 * d4Graph K ε)) =
        MulAut.conj g₃ * (exactNormalAut Tag.D4 K a₃ (σ₁ * σ₂) 0 * d4Graph K ε) := by
  refine ⟨g₁ * exactNormalAut Tag.D4 K a₁ σ₁ 0 g₂,
    fun j => a₁ j * Units.map σ₁.toRingHom.toMonoidHom (a₂ ((exactPerm Tag.D4 0).symm j)), ?_⟩
  have h1 : (MulAut.conj g₁ * exactNormalAut Tag.D4 K a₁ σ₁ 0) *
      (MulAut.conj g₂ * (exactNormalAut Tag.D4 K a₂ σ₂ 0 * d4Graph K ε)) =
      MulAut.conj g₁ * ((exactNormalAut Tag.D4 K a₁ σ₁ 0 * MulAut.conj g₂) *
        (exactNormalAut Tag.D4 K a₂ σ₂ 0 * d4Graph K ε)) := by
    simp only [mul_assoc]
  rw [h1, mul_conj_eq, map_mul]
  have h2 : MulAut.conj (exactNormalAut Tag.D4 K a₁ σ₁ 0 g₂) * exactNormalAut Tag.D4 K a₁ σ₁ 0 *
      (exactNormalAut Tag.D4 K a₂ σ₂ 0 * d4Graph K ε) =
      MulAut.conj (exactNormalAut Tag.D4 K a₁ σ₁ 0 g₂) *
        (exactNormalAut Tag.D4 K a₁ σ₁ 0 * exactNormalAut Tag.D4 K a₂ σ₂ 0 * d4Graph K ε) := by
    simp only [mul_assoc]
  rw [mul_assoc (MulAut.conj g₁)  (MulAut.conj (exactNormalAut Tag.D4 K a₁ σ₁ 0 g₂)), h2,
    exactNormalAut_mul, ← mul_assoc, ← mul_assoc]

end NormalForm

end CFSG.LieType.SeitzGeneration.ExcWideThree
