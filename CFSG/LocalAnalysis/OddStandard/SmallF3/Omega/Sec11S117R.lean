module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step117R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R → JMod z R = secD K1 K2 R ⊔ secQ K1 K2

end CFSG.OddStandard.SmallF3.Omega
