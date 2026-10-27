module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82StepZ4Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → IsZ4Pow4 (secV t S L E) → S ≤ L ⊔ centralizer (L : Set G)

end CFSG.OddStandard.SmallF3.Omega
