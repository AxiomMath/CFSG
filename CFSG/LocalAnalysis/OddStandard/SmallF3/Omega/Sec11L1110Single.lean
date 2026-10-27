module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step1110Single : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ R → h⁻¹ * t * h ∉ secD K1 K2 R →
        (∀ a ∈ twoCoreIn K1, h⁻¹ * t * h * a * (h⁻¹ * t * h)⁻¹ ∈ twoCoreIn K1) →
        (∀ a ∈ twoCoreIn K2, h⁻¹ * t * h * a * (h⁻¹ * t * h)⁻¹ ∈ twoCoreIn K2) →
          (ActsTrivModZ z (h⁻¹ * t * h) (twoCoreIn K1) ↔
            ActsTrivModZ z (h⁻¹ * t * h) (twoCoreIn K2))

end CFSG.OddStandard.SmallF3.Omega
