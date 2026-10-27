module

public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def NoU2Triple (G : Type) [Group G] : Prop :=
  ¬ ∃ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K

section Vocab

variable {G : Type} [Group G]

@[expose] def IsEStar (A : Subgroup G) : Prop :=
  CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ pRank 2 G

@[expose] def IsBalancedWrt (A : Subgroup G) : Prop :=
  ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
    pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊓ centralizer ({y} : Set G) =
      centralizer ({x} : Set G) ⊓ pPrimeCoreOf 2 (centralizer ({y} : Set G))

@[expose] def IsTrivialPumpupAt (x : G) (K : Subgroup G) (t : G) : Prop :=
  ∀ K' : Subgroup G, PumpUpLT 2 x K t K' →
    x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K)

structure IsTerminallyUnbalancing (x y : G) (K : Subgroup G) : Prop where
  unbalancing : IsUnbalancingTriple x y K
  trivialPumpups : ∀ z : G, orderOf z = 2 → z ∈ CxK x K → z * y = y * z → IsTrivialPumpupAt x K z
  sylow : ∀ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) → ∀ z ∈ Q, orderOf z = 2 →
    (∀ q ∈ Q, z * q = q * z) → z * y = y * z → ∀ K' : Subgroup G, PumpUpLT 2 x K z K' →
      IsSylowOf 2 Q (CxK z K')

structure Hyp4Core (x y : G) (K : Subgroup G) : Prop where
  unbalancing : IsUnbalancingTriple x y K
  trivialPumpups : ∀ t : G, orderOf t = 2 → t ∈ CxK x K → t * y = y * t → IsTrivialPumpupAt x K t

structure Hyp4A (x y : G) (K : Subgroup G) : Prop extends Hyp4Core x y K where
  nontrivial : ∃ (t : G) (K' : Subgroup G), PumpUpLT 2 x K t K' ∧
    ¬ (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K))

structure Hyp4B (x y : G) (K : Subgroup G) : Prop extends Hyp4Core x y K where
  notTerminal : ¬ IsTwoTerminal x K
  sylow : ∀ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) → ∀ t ∈ Q, orderOf t = 2 →
    (∀ q ∈ Q, t * q = q * t) → t * y = y * t → ∀ K' : Subgroup G, PumpUpLT 2 x K t K' →
      IsSylowOf 2 Q (CxK t K')

end Vocab

@[expose] def St1Thm7 (G : Type) [Group G] : Prop := L2Sub G InC2

@[expose] def St1Prop41 (G : Type) [Group G] : Prop :=
  (∀ (x y : G) (K : Subgroup G), Hyp4A x y K → 5 ≤ pRank 2 G) ∧
    (∀ (x y : G) (K : Subgroup G), Hyp4B x y K → 5 ≤ pRank 2 G)

@[expose] def St1Prop51 (G : Type) [Group G] : Prop :=
  ∀ (x y : G) (K R : Subgroup G), IsUnbalancingTriple x y K → IsStar2 x →
    IsSylowOf 2 R (NxK x K) → y ∈ R →
      pRank 2 ↥R = pRank 2 G ∧
      (HasL2Model (kBar K) (fun q => q = 9) ∨
        (IsL34Quotient (kBar K) ∧ CFSG.IsElementaryAbelian 2 ↥(center (kBar K)) ∧
          Nat.card ↥(center (kBar K)) ≤ 4)) ∧
      ∃ (z : G) (J : Subgroup G), PumpUpLT 2 x K z J ∧ IsTrivialPumpupAt x K z ∧
        IsTerminallyUnbalancing z y J ∧ z ∈ R ∧ (∀ r ∈ R, z * r = r * z) ∧ z ∈ CxK x K ∧ IsStar2 z

@[expose] def St1Thm4 (G : Type) [Group G] : Prop := ∀ A : Subgroup G, IsEStar A → IsBalancedWrt A

@[expose] def St1Thm5 (G : Type) [Group G] : Prop :=
  ∀ x : G, IsStar2 x → pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥

@[expose] def St1Thm6 (G : Type) [Group G] : Prop :=
  ∀ x : G, orderOf x = 2 → pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥

end CFSG.GH74.GLS
