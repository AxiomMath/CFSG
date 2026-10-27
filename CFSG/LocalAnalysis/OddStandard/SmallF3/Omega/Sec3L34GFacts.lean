module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def SimpleFStarQuotient (Y : Type) [Group Y] : Prop :=
  SmallF3OmegaQuotient Y ∨ SmallF3StarQuotient Y

@[expose] def Asc82FactO3Cent : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (H : Subgroup A), H.Normal →
    centralizer (H : Set A) = ⊥ → SimpleFStarQuotient H →
    ∀ a : A, orderOf a = 2 →
      CFSG.inSubgroup (CFSG.pCore 3) (H ⊓ centralizer ({a} : Set A)) = ⊥

@[expose] def Asc82FactCent3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (H : Subgroup A), H.Normal →
    centralizer (H : Set A) = ⊥ → SimpleFStarQuotient H →
    ∀ a : A, orderOf a = 2 → ∀ g : A, orderOf g = 3 → g * a = a * g →
      ¬ ∀ c ∈ H ⊓ centralizer ({a} : Set A), Odd (orderOf c) → g * c = c * g

@[expose] def Asc82SchurOdd3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), InFStar X → IsPGroup 3 ↥(oddCore ↥X)

@[expose] def Asc82FactNoncentralFixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I : Subgroup G), InFStar I →
    ∀ x : G, orderOf x = 2 → x ∈ normalizer (I : Set G) →
      ∃ e ∈ I ⊓ centralizer ({x} : Set G), orderOf e = 2 ∧ ¬ ∀ g ∈ I, e * g = g * e

@[expose] def Asc82FactPocketComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), InFStar H →
    ∀ (y : G) (B : Subgroup G), orderOf y = 2 → Sl23PocketIn H y B →
    ∀ t : G, orderOf t = 2 → t ∈ normalizer (H : Set G) → B ≤ centralizer ({t} : Set G) →
      (∀ c ∈ centralizer (H : Set G), t ≠ y * c) →
      ∃ J : Subgroup G, IsComponentIn J (H ⊓ centralizer ({t} : Set G)) ∧ InFStar J ∧ y ∈ J ∧
        IsI4PlusIn J y

@[expose] def Asc82FactPocketLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), InFStar H →
    ∀ a : G, orderOf a = 2 → a ∈ normalizer (H : Set G) →
    ∀ J : Subgroup G, IsComponentIn J (H ⊓ centralizer ({a} : Set G)) →
    ∀ b ∈ J, IsI4PlusIn J b → IsI4PlusIn H b

end CFSG.OddStandard.SmallF3.Omega
