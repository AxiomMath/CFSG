module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropALift

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint

theorem thompson_burgoyne_of_inputs
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hCI : StandardRecognition.ClassicalInvolutionTheoremModels) (hA : BurgoynePropA)
    (hB : BurgoynePropB) (hC : BurgoynePropC) (hL34 : L34PumpUpExclusion)
    (hSol : SolomonSignalizerInput) (hHe : HeldTrivialMultiplier)
    (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (x y : X) (L : Subgroup X)
    (hT : UnbalancedLayer.GSUnbalancingTriple x y L) :
    (∃ n : ℕ, Odd n ∧ 9 ≤ n ∧ Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* NativeSporadic.He) ∨
        LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2) :=
  have hI : TBInputs := ⟨hUc, hSch, hCI, hA, hB, hC, hL34, hSol, hHe, hGA, hGC⟩
  thompson_burgoyne_of_exclusions hUc hHe (chevalleyExclusion_of_inputs hI)
    (coverExclusion_of_inputs hI) X hnonab hK hz hU x y L hT

end CFSG.ComponentClassification.TBLit
