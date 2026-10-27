module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def BelowSec (P : GroupPred) (H : Type) [Group H] [Finite H] : Prop :=
  Balance.UHered H ∧
    ∀ (X : Type) [Group X] [Finite X], IsSectionOf X H → Nat.card X < Nat.card H → P X

@[expose] def StepSec (P : GroupPred) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], BelowSec P H → P H

theorem BelowSec.uHered {P : GroupPred} {H : Type} [Group H] [Finite H] (h : BelowSec P H) :
    Balance.UHered H :=
  h.1

theorem BelowSec.apply {P : GroupPred} {H X : Type} [Group H] [Finite H] [Group X] [Finite X]
    (h : BelowSec P H) (hX : IsSectionOf X H) (hlt : Nat.card X < Nat.card H) : P X :=
  h.2 X hX hlt

theorem BelowSec.of_section_le {P : GroupPred} {H G : Type} [Group H] [Finite H] [Group G]
    [Finite G] (h : BelowSec P H) (hG : IsSectionOf G H) (hle : Nat.card G ≤ Nat.card H) :
    BelowSec P G :=
  ⟨h.1.of_section hG, fun X _ _ hX hlt => h.2 X (hX.trans hG) (lt_of_lt_of_le hlt hle)⟩

theorem holds_of_stepSec {P : GroupPred} (hP : StepSec P) (H : Type) [Group H] [Finite H]
    (hH : Balance.UHered H) : P H := by
  have key : ∀ n : ℕ, ∀ (H : Type) [Group H] [Finite H], Nat.card H = n → Balance.UHered H →
      P H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H _ _ hn hH
      exact hP H ⟨hH, fun X _ _ hX hlt => ih _ (hn ▸ hlt) X rfl (hH.of_section hX)⟩
  exact key _ H rfl hH

end CFSG.EvenSporadicStandard.Induction
