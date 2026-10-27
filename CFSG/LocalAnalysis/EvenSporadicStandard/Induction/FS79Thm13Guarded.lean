module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78
open CFSG.SignalizerFunctorTheorem (IsSectionOf)
open scoped commutatorElement

@[expose] def FS79Thm13UseAt (H : Type) [Group H] [Finite H] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ (N : Subgroup H), FStarSimple N → (∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N) →
    ∀ K : Subgroup H, MaximalF K → CFSG.pRank 2 ↥K ≠ 1 → StdBare K

@[expose] def FS79Thm13UseHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → FS79Thm13UseAt H

@[expose] def FS79Thm13UseSec (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSectionOf X G → FS79Thm13UseAt X

theorem FS79Thm13UseHered.sec (h : FS79Thm13UseHered) {G : Type} [Group G] [Finite G]
    (hG : Balance.UHered G) : FS79Thm13UseSec G :=
  fun X _ _ hX => h X (hG.of_section hX)

theorem FS79Thm13UseSec.at {G : Type} [Group G] [Finite G] (h : FS79Thm13UseSec G) :
    FS79Thm13UseAt G :=
  h G (IsSectionOf.refl G)

end CFSG.EvenSporadicStandard.Induction
