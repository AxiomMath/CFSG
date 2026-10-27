module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOrth

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof.OddInner
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup Module
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

theorem cl24_oddLie_orthogonal {p : ℕ} (hO : Cl24OrthComp p) (hp : p.Prime)
    (hp2 : p ≠ 2) {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {e : ℕ} (he : 1 ≤ e) (hk : Nat.card k = p ^ e)
    (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)} (hM : IsComponent M)
    {Rel : ℕ → Prop}
    (hRel : ∀ f', f' = e ∨ (finrank k W = 4 ∧ f' = 2 * e) → Rel f' := by cl24_rel) :
    Cl24Q p Rel M := by
  rcases Nat.lt_or_ge (finrank k W) 3 with h3 | h3
  · have hodd : Odd (Nat.card k) := by
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
    have := CatalogueBOrthogonal.orthogonal_small_solvable Q₀ h2 hQ₀ (by omega)
    exact absurd hM (not_isComponent_of_isSolvable M)
  · exact (hO k W e he hk Q₀ hQ₀ h3 M hM).mono hRel

end CFSG.OddStandard.SmallF3.HypA2Leaves
