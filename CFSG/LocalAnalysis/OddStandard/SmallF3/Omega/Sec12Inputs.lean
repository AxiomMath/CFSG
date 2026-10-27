module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactSplit5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → IsPSp43 L → S ≤ normalizer (L : Set G) →
    centralizer (L : Set G) ⊓ S = zpowers t → IsSylow2Of (S ⊓ L) L → t ∉ L →
      ∃ X0 : Subgroup G, X0 ⊓ secB S L = ⊥ ∧ X0 ⊔ secB S L = (secM t S L ⊓ L) ⊔ S

@[expose] def Asc82Step1210N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      ∃ N0 : Subgroup G, N0 ≤ secN (secV t S L E) ∧
        (N0.subgroupOf (secN (secV t S L E))).Normal ∧
        N0.relIndex (secN (secV t S L E)) = 2 ∧ t ∉ N0

end CFSG.OddStandard.SmallF3.Omega
