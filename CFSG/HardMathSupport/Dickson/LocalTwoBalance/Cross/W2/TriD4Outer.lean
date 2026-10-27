module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Odd
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


theorem coreFreeAt_three_D4_outer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    CoreFreeAt 3 φ := by
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · exact coreFreeAt_three_D4_outer_two hf hK σ hσ φ hφ3 hφ
  · exact coreFreeAt_three_D4_outer_odd hℓ hℓ2 hℓ3 hf hK σ hσ φ hφ3 hφ

theorem trialityThreeRest_holds : TrialityThreeRest := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ φ hφ3 hφo _
  exact coreFreeAt_three_D4_outer hℓ hℓ3 hf hK σ hσ φ hφ3 hφo

theorem triD4OuterThreeBalance_holds : TriD4OuterThreeBalance := trialityThreeRest_holds

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
