module

public import CFSG.GH74.GLS.C3.Layer1.EvenMax
public import CFSG.GH74.GLS.TwoThin.Struct
public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.P85

open Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin

variable {G : Type} [Group G]

abbrev Mb (M : Subgroup G) : Type := barQ ↥M

@[expose] def imgM (M X : Subgroup G) : Subgroup (Mb M) :=
  (X.subgroupOf M).map (barMk ↥M)

@[expose] def IsTerminalSub {X : Type} [Group X] (K : Subgroup X) : Prop :=
  ∀ y : X, orderOf y = 2 → (∀ k ∈ K, y * k = k * y) →
    IsCompIn (centralizer ({y} : Set X)) K

@[expose] def Ivk73Alt {X : Type} [Group X] (K L : Subgroup X) : Prop :=
  L = ⊤ ∧ ∃ n ∈ ({5, 6, 7} : Finset ℕ),
    Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin n)) ∧
    Nonempty (↥L ≃* alternatingGroup (Fin (n + 4)))

@[expose] def Ivk73Spor {X : Type} [Group X] (K L : Subgroup X) : Prop :=
  Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
    ((NativeSporadic.IsSporadic ↥L .M12 ∧ Nat.card X = 2 * Nat.card ↥L) ∨
      (NativeSporadic.IsSporadic ↥L .J2 ∧ (L = ⊤ ∨ Nat.card X = 2 * Nat.card ↥L)))

section Situation

variable [Finite G]

structure P85Setup (x y : G) (K T S M L : Subgroup G) : Prop where
  hG : C3Hyp G
  choice : Th2Choice x y K T S M
  KM : K ≤ M
  hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)
  hL : IsMinSubnormalIn K M L
  ne : imgM M K ≠ imgM M L

structure P85Struct (x y : G) (K T S M L : Subgroup G) : Prop extends P85Setup x y K T S M L where
  terminal : IsTerminalSub (imgM M K)
  socle : IsSimpleSocle (imgM M L) ⊤
  Qelem : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K)
  Qcard : Nat.card ↥(T ⊓ CxK x K) = 4

end Situation

end CFSG.GH74.GLS.Th2.P85

namespace CFSG.GH74.GLS

open Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85

@[expose] def B_thm2_p86 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Setup x y K T S M L → 2 ≤ pRank 2 ↥(T ⊓ CxK x K) → IsTerminalSub (imgM M K) →
      IsSimpleSocle (imgM M L) ⊤

@[expose] def B_thm2_p85_alt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Struct x y K T S M L → Ivk73Alt (imgM M K) (imgM M L) → False

@[expose] def B_thm2_p85_spor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Struct x y K T S M L → Ivk73Spor (imgM M K) (imgM M L) → False

end CFSG.GH74.GLS
