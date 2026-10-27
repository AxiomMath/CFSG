module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82E16Good : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsOm6P K →
    ∀ B : Subgroup G, IsElemAb2 B 4 → B ≤ K → 5 ∣ Nat.card ↥(K ⊓ normalizer (B : Set G)) →
      ∃ P : Subgroup G, IsSylow2Of P K ∧ IsNormalE16In P B

end CFSG.OddStandard.SmallF3.Omega
