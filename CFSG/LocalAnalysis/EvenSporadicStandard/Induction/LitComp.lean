module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Relations
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

@[expose] def twoLayerIn {H : Type} [Group H] (X : Subgroup H) : Subgroup H :=
  (CFSG.pLayer ↥X 2).map X.subtype

@[expose] def FS79Lemma15Monotonicity : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (S : Subgroup G), IsPGroup 2 S →
    ∀ T : Subgroup G, T ≤ S → twoLayerIn (centralizer (S : Set G)) ≤
      twoLayerIn (centralizer (T : Set G))

@[expose] def FS79Thm13Use : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ (N : Subgroup H), FStarSimple N → (∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N) →
    ∀ K : Subgroup H, MaximalF K → CFSG.pRank 2 ↥K ≠ 1 → StdBare K

end CFSG.EvenSporadicStandard.Induction
