module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82CorIII : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G),
    Sec3SettingLB G t L → ∀ z : G, ¬ IsI4PlusIn (⊤ : Subgroup G) z

end CFSG.OddStandard.SmallF3.Omega
