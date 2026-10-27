module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Sec123NoS5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E X : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → Sec12X t S L E X → Sec122Alt1 (secV t S L E) X →
      ¬ Nonempty (↥X ≃* Equiv.Perm (Fin 5))

end CFSG.OddStandard.SmallF3.Omega
