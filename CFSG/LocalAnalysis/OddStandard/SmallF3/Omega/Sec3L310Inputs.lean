module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def IsOmegaPlusIn (Y : Subgroup G) : Prop :=
  InF Y ∧ LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1

@[expose] def pocketCore2 (Y : Subgroup G) (z : G) : Subgroup G :=
  ⨆ (K : Subgroup G) (_ : Sl23PocketIn Y z K), CFSG.inSubgroup (CFSG.pCore 2) K

@[expose] def twoU43Comps (Y : Subgroup G) (d : G) : Subgroup G :=
  ⨆ (K : Subgroup G) (_ : IsComponentIn K (Y ⊓ centralizer ({d} : Set G)) ∧ d ∈ K ∧
      IsTwoU43 (↥K ⧸ oddCore ↥K)), K

@[expose] def Asc82OmegaPlusInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsOmegaPlusIn Y →
    ∀ w : G, orderOf w = 2 → w ∈ Y → ¬ IsI4PlusIn Y w →
      ∃ (X : Subgroup G) (u : G), IsComponentIn X (Y ⊓ centralizer ({w} : Set G)) ∧ w ∈ X ∧
        IsTwoU43 (↥X ⧸ oddCore ↥X) ∧ IsI4PlusIn X u ∧ ∃ a ∈ Y, a⁻¹ * w * a = u * w

@[expose] def Asc82OmegaPlusOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsOmegaPlusIn Y →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (Y : Set G) →
      (¬ ∃ a ∈ Y, ∃ c ∈ centralizer (Y : Set G), s = a * c) →
        ∃ u : G, u ∈ CFSG.inSubgroup CFSG.layer (Y ⊓ centralizer ({s} : Set G)) ∧
          orderOf u = 2 ∧ ∃ a ∈ Y, a⁻¹ * s * a = u * s

@[expose] def Asc82OmegaPlusClosure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsOmegaPlusIn Y →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (Y : Set G) →
      ∀ J : Subgroup G, IsComponentIn J (Y ⊓ centralizer ({s} : Set G)) → InFStar J

@[expose] def Asc82OmegaPlusPocketedConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsOmegaPlusIn Y →
    ∀ z₁ z₂ : G, IsI4PlusIn Y z₁ → IsI4PlusIn Y z₂ → ∃ a ∈ Y, a⁻¹ * z₁ * a = z₂

@[expose] def Asc82OmegaPlusPocketLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsOmegaPlusIn Y →
    ∀ a : G, orderOf a = 2 → a ∈ normalizer (Y : Set G) →
      ∀ X : Subgroup G, IsComponentIn X (Y ⊓ centralizer ({a} : Set G)) →
        ∀ u : G, IsI4PlusIn X u → IsI4PlusIn Y u

@[expose] def Asc82OmegaPlusGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsOmegaPlusIn Y →
    ∀ z : G, IsI4PlusIn Y z →
      Y ≤ ⨆ (d : G) (_ : orderOf d = 2 ∧ d ∈ pocketCore2 Y z ∧ ¬ IsI4PlusIn Y d),
        twoU43Comps Y d

@[expose] def Asc82OmegaPlusCStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1 → InCStar L

end CFSG.OddStandard.SmallF3.Omega
