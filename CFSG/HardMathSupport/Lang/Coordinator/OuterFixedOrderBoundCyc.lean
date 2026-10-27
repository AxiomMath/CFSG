module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAll

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OuterFixedOrderBoundCyc : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n ℓ f : ℕ),
    StatedLieAdmissible t n ℓ f → CFSG.Blueprint.LieModel K t n ℓ f → t ≠ .Tits →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) →
      ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) → ¬ (t = .trialityD4 ∧ p = 3) →
    ∀ α : MulAut K, α ^ p = 1 → α ∉ inner K →
      ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator t n (ℓ ^ f₀)

theorem outerFixedOrderBoundCyc_holds : OuterFixedOrderBoundCyc := by
  intro K _ _ t n ℓ f hadm hmodel ht p hp hp2 hdiv hD4 hT3 α hαp hαin
  by_cases htri : t = .trialityD4
  · subst htri
    exact outerFixedOrder_trialityD4_of_ne_three K n ℓ f hadm hmodel ht p hp hp2 hdiv hD4
      (fun h3 => hT3 ⟨rfl, h3⟩) α hαp hαin
  · have hall : OuterFixedOrderBoundAt t := by
      cases t with
      | PSL => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL
      | PSU => exact outerFixedOrderBoundAt_PSU
      | PSp => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp
      | POmegaOdd => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaOdd
      | POmegaPlus => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaPlus
      | POmegaMinus => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaMinus
      | G2 => exact E6Descent.outerFixedOrderBoundAt_G2
      | F4 => exact E6Descent.outerFixedOrderBoundAt_F4
      | E6 => exact outerFixedOrderBoundAt_E6
      | E7 => exact E6Descent.outerFixedOrderBoundAt_E7
      | E8 => exact E6Descent.outerFixedOrderBoundAt_E8
      | twistedE6 => exact outerFixedOrderBoundAt_twistedE6
      | trialityD4 => exact absurd rfl htri
      | twistedB2 => exact outerFixedOrderBoundAt_twistedB2
      | twistedG2 => exact outerFixedOrderBoundAt_twistedG2
      | twistedF4 => exact outerFixedOrderBoundAt_twistedF4
      | Tits => exact outerFixedOrderBoundAt_Tits
    rcases hall K n ℓ f hadm hmodel ht p hp hp2 hdiv hD4 α hαp hαin with h | ⟨h, -⟩
    · exact h
    · exact absurd h htri

end CFSG.HardMathSupport.Lang.Coordinator
