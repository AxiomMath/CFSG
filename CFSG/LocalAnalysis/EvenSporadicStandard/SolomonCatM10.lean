module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Solomon

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open

@[expose] def CatM10AlmostSimple : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), S.Normal → IsSimpleGroup ↥S →
    CFSG.Blueprint.Catalog ↥S → centralizer (S : Set K) = ⊥ → ∀ z : K, orderOf z = 2 →
      fusionOddCore ↥(centralizer ({z} : Set K)) = ⊥ →
      Fin76b.SolomonM10Hyp K z → Fin76b.SolomonM10Conclusion K z

end CFSG.EvenSporadicStandard
