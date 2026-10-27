module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def Asc82FactSplitModel : Prop :=
  ∃ X : Subgroup (Equiv.Perm (Fin 45)),
    X ≤ QA45.originalSubgroup ⊓ normalizer (B0 : Set (Equiv.Perm (Fin 45))) ∧ X ⊓ B0 = ⊥ ∧
      ∀ a ∈ QA45.originalSubgroup ⊓ normalizer (B0 : Set (Equiv.Perm (Fin 45))),
        ∃ x ∈ X, ∃ b ∈ B0, a = x * b

end CFSG.OddStandard.SmallF3.Omega
