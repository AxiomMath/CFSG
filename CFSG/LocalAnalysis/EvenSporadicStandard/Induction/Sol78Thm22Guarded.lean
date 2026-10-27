module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def Sol78Thm22At (H : Type) [Group H] [Finite H] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ (N : Subgroup H), FStarSimple N → N.index ≤ 2 → ∀ A : Subgroup H,
    Maximal A → 3 ≤ CFSG.pRank 2 ↥A → StdBare A

@[expose] def Sol78Thm22Hered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Sol78Thm22At H

@[expose] def Sol78Thm22Sec (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSectionOf X H → Sol78Thm22At X

theorem Sol78Thm22Hered.sec (h : Sol78Thm22Hered) {H : Type} [Group H] [Finite H]
    (hH : Balance.UHered H) : Sol78Thm22Sec H :=
  fun X _ _ hX => h X (hH.of_section hX)

theorem Sol78Thm22Sec.at {H : Type} [Group H] [Finite H] (h : Sol78Thm22Sec H) :
    Sol78Thm22At H :=
  h H (IsSectionOf.refl H)

end CFSG.EvenSporadicStandard.Induction
