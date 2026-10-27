module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def IsPSp43 {G : Type} [Group G] (L : Subgroup G) : Prop :=
  LieModel ↥L .PSp 2 3 1

@[expose] def Asc82FactSylow5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ P : Subgroup G, IsSylow2Of P L →
      Nat.card (centerIn P) = 2 ∧
        ∀ g ∈ normalizer (L : Set G), (∀ p ∈ P, g * p = p * g) →
          g ∈ centralizer (L : Set G) ⊔ centerIn P

@[expose] def Asc82FactOut5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) ≤ 2

@[expose] def Asc82FactB5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ P : Subgroup G, IsSylow2Of P L →
      ∃ B : Subgroup G, IsMaxElemAbelianIn P B ∧ Nat.card B = 2 ^ 4 ∧
        (∀ B' : Subgroup G, B' ≤ P → IsMulCommutative B' → Nat.card B' = 2 ^ 4 → B' = B) ∧
        centralizer (B : Set G) ⊓ L = B ∧
        ∃ φ : (Fin 5 → ZMod 2) → G,
          IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) (alternatingGroup (Fin 5)) ∧
          (∀ v, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L (φ v)) ∧
          (∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L (φ v)) ∧
          ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (B : Set G),
            ∃ σ : Equiv.Perm (Fin 5), ∀ v, IsEvenVec v → g * φ v * g⁻¹ = φ (permVec σ v)

@[expose] def Asc82FactPockets5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ z : G, IsI4PlusIn L z →
      ∃ K1 K2 : Subgroup G, Sl23PocketIn L z K1 ∧ Sl23PocketIn L z K2 ∧ K1 ≠ K2 ∧
        (∀ K : Subgroup G, Sl23PocketIn L z K → K = K1 ∨ K = K2) ∧ ⁅K1, K2⁆ = ⊥ ∧
        oTwoRes (L ⊓ centralizer ({z} : Set G)) = K1 ⊔ K2 ∧
        (K1 ⊔ K2).relIndex (L ⊓ centralizer ({z} : Set G)) = 2 ∧
        ∀ g ∈ L ⊓ centralizer ({z} : Set G), g ∉ K1 ⊔ K2 → CFSG.conjugate K1 g = K2

@[expose] def Asc82FactN7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ x ∈ L, orderOf x = 2 →
      ∀ P : Subgroup G, IsSylow2Of P (L ⊓ centralizer ({x} : Set G)) → x ∈ ⁅P, P⁆

end CFSG.OddStandard.SmallF3.Omega
