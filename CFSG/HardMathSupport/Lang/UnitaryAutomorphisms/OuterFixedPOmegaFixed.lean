module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer

public section

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem matrixProjectiveConjugationHom_eq_fieldAutT (S : SubfieldSetup k Q₀ Q' σ p)
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ) :
    matrixProjectiveConjugationHom Q' g' = fieldAutT Q' σ S.hQσ := by
  unfold fieldAutT
  refine CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q' (g := g')
    (h := fieldPair Q' σ S.hQσ) 1 ?_ hr
  rw [hl, fieldPair_left]
  simp

theorem card_fixedSubgroup_eq_subfieldFixedGroup (S : SubfieldSetup k Q₀ Q' σ p)
    {β : MulAut (matrixProjectiveDerived Q)}
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q' g' (Θ x)) :
    Nat.card (fixedSubgroup β) = Nat.card (subfieldFixedGroup k Q₀ Q') := by
  have h1 := CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_eq_of_intertwine Θ β _ fun x => (hΘ x).symm
  rw [h1, matrixProjectiveConjugationHom_eq_fieldAutT S g' hl hr]
  congr 1
  have : fixedSubgroup (fieldAutT Q' σ S.hQσ) = subfieldFixedGroup k Q₀ Q' := by
    ext t
    exact fieldAutT_apply_iff S t
  rw [this]

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
