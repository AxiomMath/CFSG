module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitComp

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

@[expose] def FS79Lemma15At (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (S : Subgroup G), IsPGroup 2 S →
    (∀ T : Subgroup G, T ≤ S → twoLayerIn (centralizer (S : Set G)) ≤
      twoLayerIn (centralizer (T : Set G))) ∧
    (CFSG.oddCore G = ⊥ → twoLayerIn (centralizer (S : Set G)) = layerIn (centralizer (S : Set G)))

end CFSG.EvenSporadicStandard.Induction
