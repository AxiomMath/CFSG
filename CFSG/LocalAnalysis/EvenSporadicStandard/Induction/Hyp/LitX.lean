module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def OddLieCompNotSporadic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' →
    CFSG.Blueprint.OddLieType ↥N' → ∀ t : Y, orderOf t = 2 → ∀ A : Subgroup Y,
      IsCompIn A (centralizer ({t} : Set Y)) → ∀ s'' : TauCeti.SporadicName,
        ¬ IsSporadic (↥A ⧸ center ↥A) s''

structure Hyp31LitX : Prop where
  oddLie : OddLieCompNotSporadic

theorem oddLieExcl_of_lit (h : OddLieCompNotSporadic) (s' : TauCeti.SporadicName) :
    OddLieExcl s' := by
  intro Y _ _ N' hN hlie A hA hcov
  obtain ⟨-, t, ht2, hc⟩ := hA
  exact h Y N' hN hlie t ht2 A hc s' hcov.2.2

end CFSG.EvenSporadicStandard.Induction.Hyp
