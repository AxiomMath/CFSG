module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

@[expose] def IVK_7_3_g4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N L K Q : Subgroup G),
    Gen4 ↥N → GHList ↥L → IsKGroupNative ↥N →
    (L ≤ N ∧ (∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L) ∧ IsSimpleGroup ↥L ∧
      ∀ n ∈ N, (∀ l ∈ L, n * l = l * n) → n = 1) →
    K ≤ L → IsQuasisimple ↥K → InU2 (↥K ⧸ pPrimeCore 2 ↥K) →
    IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N) → 2 ≤ pRank 2 ↥Q →
    (∀ y ∈ N, orderOf y = 2 → y ∈ centralizer (K : Set G) →
      IsCompIn (centralizer ({y} : Set G) ⊓ N) K) →
    IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4 ∧
      ((Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
          NativeSporadic.IsSporadic ↥L .M12 ∧ Nat.card ↥N = 2 * Nat.card ↥L) ∨
        (Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
          NativeSporadic.IsSporadic ↥L .J2 ∧ (N = L ∨ Nat.card ↥N = 2 * Nat.card ↥L)) ∨
        (N = L ∧ ∃ n ∈ ({5, 6, 7} : Finset ℕ),
          Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin n)) ∧
          Nonempty (↥L ≃* alternatingGroup (Fin (n + 4)))) ∨
        (IsL34Quotient (↥K ⧸ pPrimeCore 2 ↥K) ∧ center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ ∧
          NativeSporadic.IsSporadic ↥L .Suz) ∨
        (IsL34Quotient (↥K ⧸ pPrimeCore 2 ↥K) ∧
          IsElementaryAbelian 2 ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ∧
          Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 4 ∧ NativeSporadic.IsSporadic ↥L .He))

end CFSG.GH74.GLS.IVK
