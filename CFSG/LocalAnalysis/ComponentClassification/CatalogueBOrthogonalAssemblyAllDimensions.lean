module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssembly

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalAssembly

universe u v

variable {K : Type u} [Field K] [Finite K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_all_dimensional_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  orthogonal_pComponent_quasisimple hodd Q hQ
    (three_le_finrank_of_pComponent hodd Q hQ p L hL) p L hL

theorem odd_orthogonal_all_dimensional_isometry_p_components (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
      (Module.finrank K V ≤ 2 →
        Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
          ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
            ¬ CFSG.IsPComponent p L) := by
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact orthogonal_all_dimensional_pComponent_quasisimple hodd Q hQ p L hL
  · intro hdim
    obtain ⟨hsolvable, hno⟩ := orthogonal_small_solvable_no_pComponents hodd Q hQ hdim
    exact ⟨hsolvable, fun p _ L => hno p L⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalAssembly

