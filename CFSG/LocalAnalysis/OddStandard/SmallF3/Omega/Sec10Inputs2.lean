module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactCentK5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ (z : G), orderOf z = 2 → ∀ (K1 K2 : Subgroup G),
      Sl23PocketIn L z K1 → Sl23PocketIn L z K2 → K1 ≠ K2 →
      ∀ y ∈ normalizer (L : Set G), (∀ k ∈ K1 ⊔ K2, y * k = k * y) →
        y ∈ centralizer (L : Set G) ⊔ zpowers z

@[expose] def Asc82FactCentZ5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ z : G, IsI4PlusIn L z → Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 576

@[expose] def Asc82FactCentB5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ P : Subgroup G, IsSylow2Of P L →
      ∀ g ∈ normalizer (L : Set G), (∀ b ∈ JElem P, g * b = b * g) →
        g ∈ JElem P ⊔ centralizer (L : Set G)

@[expose] def Asc82FactAutAb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I : Subgroup G), CFSG.IsQuasisimple ↥I →
    (LieModel (I ⧸ oddCore I) .PSp 2 3 1 ∨ LieModel (I ⧸ oddCore I) .PSL 2 3 4) →
      ∀ Y : Subgroup G, Y ≤ normalizer (I : Set G) → Y ⊓ centralizer (I : Set G) = ⊥ →
        IsPGroup 2 Y → IsMulCommutative Y → Nat.card Y ≤ 16

end CFSG.OddStandard.SmallF3.Omega
