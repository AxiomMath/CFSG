module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockJ2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType

theorem projConj_scalar_mul {N : ℕ} {K : Type} [Field K]
    (H : Subgroup (GL (Fin N) K)) (σ : Kˣ) (D : GL (Fin N) K)
    (hDN : D ∈ Subgroup.normalizer (H : Set (GL (Fin N) K)))
    (hN : Matrix.GeneralLinearGroup.scalar (Fin N) σ * D ∈
      Subgroup.normalizer (H : Set (GL (Fin N) K))) :
    TableB.projConj H ⟨Matrix.GeneralLinearGroup.scalar (Fin N) σ * D, hN⟩ =
      TableB.projConj H ⟨D, hDN⟩ := by
  have hσN : Matrix.GeneralLinearGroup.scalar (Fin N) σ ∈
      Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
    TableB.scalar_mem_normalizer H ⟨σ, rfl⟩
  have h1 : (⟨Matrix.GeneralLinearGroup.scalar (Fin N) σ * D, hN⟩ :
      Subgroup.normalizer (H : Set (GL (Fin N) K))) =
      ⟨Matrix.GeneralLinearGroup.scalar (Fin N) σ, hσN⟩ * ⟨D, hDN⟩ := Subtype.ext rfl
  rw [h1, map_mul]
  have h2 : TableB.projConj H
      ⟨Matrix.GeneralLinearGroup.scalar (Fin N) σ, hσN⟩ = 1 := by
    rw [show (⟨Matrix.GeneralLinearGroup.scalar (Fin N) σ, hσN⟩ :
        Subgroup.normalizer (H : Set (GL (Fin N) K))) =
        ⟨Matrix.GeneralLinearGroup.scalar (Fin N) σ,
          TableB.scalar_mem_normalizer H ⟨σ, rfl⟩⟩ from Subtype.ext rfl,
      TableB.projConj_of_scalar H ⟨σ, rfl⟩]
  rw [h2, one_mul]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
