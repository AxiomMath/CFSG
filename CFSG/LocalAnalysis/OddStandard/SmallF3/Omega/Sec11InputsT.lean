module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step1110Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ S →
        ¬ InducesTypeSome L (h⁻¹ * t * h) 5 1 2 1

end CFSG.OddStandard.SmallF3.Omega
