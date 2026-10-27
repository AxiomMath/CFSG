module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step105S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → (¬ ∃ g : G, g⁻¹ * t * g = t * z) → IsSylow2Of S ⊤

@[expose] def Asc82Step105C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → (¬ ∃ g : G, g⁻¹ * t * g = t * z) →
      IsStrClosedModZ t z (secW t K1 K2)

@[expose] def Asc82Step105T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → (¬ ∃ g : G, g⁻¹ * t * g = t * z) →
      ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ S → h⁻¹ * t * h = t

@[expose] def Asc82Step105Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → IsSylow2Of S ⊤ →
      (∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ S → h⁻¹ * t * h = t) →
        IsI4PlusIn (⊤ : Subgroup G) z

end CFSG.OddStandard.SmallF3.Omega
