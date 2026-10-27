module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt413

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.IVK.Proofs2

@[expose] def IVK413H : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) (q : ℕ), K.Normal → Odd q → 3 < q →
    IsG2Sp4L4U4_fixed ↥K q → centralizer (K : Set H) = ⊥ →
      ∀ z : H, z ∈ K → (∃ S : Sylow 2 H, z ∈ (S : Subgroup H) ∧ orderOf z = 2 ∧
          ∀ x ∈ (S : Subgroup H) ⊓ K, x * z = z * x) →
        (pPrimeCore 2 ↥(centralizer ({z} : Set H))).map (centralizer ({z} : Set H)).subtype ≠ ⊥ →
          (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ¬ ((q : ℤ) ≡ ε [ZMOD 8]) ∧ IsLnEps 4 ↥K ε q) ∧
          (Nat.card ↥(centralizer ({z} : Set H) ⊓ K) /
            Nat.card ↥((layer ↥(centralizer ({z} : Set H) ⊓ K)).map
              (centralizer ({z} : Set H) ⊓ K).subtype)).factorization 2 = 2 ∧
          (pPrimeCore 2 ↥(centralizer ({z} : Set H) ⊓ K)).map
              (centralizer ({z} : Set H) ⊓ K).subtype =
            (pPrimeCore 2 ↥(centralizer ({z} : Set H))).map (centralizer ({z} : Set H)).subtype ∧
          (∀ K₁ : Subgroup H, K₁ ≤ centralizer ({z} : Set H) ⊓ K →
            IsComponent (K₁.subgroupOf (centralizer ({z} : Set H) ⊓ K)) →
              ∀ y ∈ (pPrimeCore 2 ↥(centralizer ({z} : Set H) ⊓ K)).map
                  (centralizer ({z} : Set H) ⊓ K).subtype,
                ∀ g ∈ K ⊓ normalizer (K₁ : Set H), g * y = y * g) ∧
          (pPrimeCore 2 ↥(centralizer ({z} : Set H))).map (centralizer ({z} : Set H)).subtype ≤ K

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
