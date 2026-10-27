module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82StepZ4Comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → IsZ4Pow4 (secV t S L E) →
    ∀ s : G, orderOf s = 2 → s ∈ S → s ∉ L ⊔ centralizer (L : Set G) →
      Nat.card (secV t S L E ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ 6 → False

@[expose] def Asc82StepZ4Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → IsZ4Pow4 (secV t S L E) →
    ∀ s : G, orderOf s = 2 → s ∈ S → s ∉ L ⊔ centralizer (L : Set G) →
      Nat.card (secV t S L E ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ 6 ∨
        Nat.card (secV t S L E ⊓ centralizer ({s * t} : Set G) : Subgroup G) = 2 ^ 6

@[expose] def Asc82StepZ4NoOuterInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → IsZ4Pow4 (secV t S L E) →
    ∀ s ∈ S, s * s = 1 → s ∈ L ⊔ centralizer (L : Set G)

end CFSG.OddStandard.SmallF3.Omega
