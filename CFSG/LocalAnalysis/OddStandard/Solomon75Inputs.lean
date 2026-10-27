module

public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def Solomon44McL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 →
      IsDoubleCoverOfAlt
        (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) 8 →
      Nonempty (G ≃* Blueprint.NativeSporadic.McL)

@[expose] def Solomon44Ly : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 →
      IsDoubleCoverOfAlt
        (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) 11 →
      Nonempty (G ≃* Blueprint.NativeSporadic.Ly)

@[expose] def Solomon44NineTen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 → ∀ n : ℕ, (n = 9 ∨ n = 10) →
      ¬ IsDoubleCoverOfAlt
        (↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G))) n

end CFSG.OddStandard.Solomon75
