module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def A6KleinFacts : Prop :=
  ∀ (K : Type) [Group K], Nonempty (K ≃* alternatingGroup (Fin 6)) →
    ∀ V : Subgroup K, IsElemAbelian 2 V → 2 < Nat.card V →
      8 ≤ (Subgroup.normalizer (V : Set K)).index

end CFSG.CGT.Timmesfeld75
