module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Notation
public import CFSG.GH74.GLS.C3.Layer1.St1Defs

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section Elem

variable {G : Type} [Group G]

@[expose] def IsE (n : ℕ) (X B : Subgroup G) : Prop :=
  B ≤ X ∧ CFSG.IsElementaryAbelian 2 ↥B ∧ n ≤ pRank 2 ↥B

@[expose] def IsS (X B : Subgroup G) : Prop :=
  B ≤ X ∧ CFSG.IsElementaryAbelian 2 ↥B ∧ B = omega1 (X ⊓ centralizer (B : Set G))

@[expose] def IsSn (n : ℕ) (X B : Subgroup G) : Prop :=
  IsS X B ∧ n ≤ pRank 2 ↥B

@[expose] def IsFourSub (U A : Subgroup G) : Prop :=
  A ≤ U ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 4

@[expose] def IsConn2 (U : Subgroup G) : Prop :=
  ∀ A B : Subgroup G, IsFourSub U A → IsFourSub U B →
    Relation.ReflTransGen
      (fun A' B' : Subgroup G => IsFourSub U B' ∧ ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) A B

end Elem

section Balance

variable {G : Type} [Group G]

@[expose] def AG (B : Subgroup G) : Subgroup G :=
  ⨅ (b : G) (_ : b ∈ B ∧ b ≠ 1), pPrimeCoreOf 2 (centralizer ({b} : Set G))

@[expose] def IsKBal (k : ℕ) (A : Subgroup G) : Prop :=
  ∀ D : Subgroup G, IsE k A D → ∀ a ∈ A, a ≠ 1 →
    AG D ⊓ centralizer ({a} : Set G) ≤ pPrimeCoreOf 2 (centralizer ({a} : Set G))

@[expose] def IsWeakKBal (k : ℕ) (A : Subgroup G) : Prop :=
  ∀ D : Subgroup G, IsE k A D → ∀ a ∈ A, a ≠ 1 →
    ∀ c ∈ AG D ⊓ centralizer ({a} : Set G), ∀ b ∈ A,
      ⁅c, b⁆ ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G))

@[expose] def thetaK (k : ℕ) (B : Subgroup G) : Subgroup G :=
  ⨆ (D : Subgroup G) (_ : IsE k B D), AG D

@[expose] def thetaHalf (k : ℕ) (B : Subgroup G) : Subgroup G :=
  (⨆ (D : Subgroup G) (_ : IsE k B D), ⁅AG D, B⁆) ⊔ AG B

inductive Th2Level
  | one
  | fiveHalves
  | three
  deriving DecidableEq

namespace Th2Level

@[expose] def r : Th2Level → ℕ
  | .one => 2
  | .fiveHalves => 3
  | .three => 4

@[expose] def n : Th2Level → ℕ
  | .one => 4
  | .fiveHalves => 4
  | .three => 5

@[expose] def minRank : Th2Level → ℕ
  | .one => 3
  | .fiveHalves => 4
  | .three => 5

@[expose] def IsBal : Th2Level → Subgroup G → Prop
  | .one, A => IsKBal 1 A
  | .fiveHalves, A => IsKBal 3 A ∧ IsWeakKBal 2 A
  | .three, A => IsKBal 3 A

@[expose] def theta : Th2Level → Subgroup G → Subgroup G
  | .one, B => thetaK 1 B
  | .fiveHalves, B => thetaHalf 2 B
  | .three, B => thetaK 3 B

end Th2Level

end Balance

section Std

variable {G : Type} [Group G]

@[expose] def IsV2StarStar (x y : G) (K : Subgroup G) : Prop :=
  IsV2StarTriple x y K ∧
    (HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(CxK x K) = 2 →
      (∃ B : Subgroup G, IsE 4 ⊤ B ∧ ¬ IsBalancedWrt B) →
        IsUnbalancingTriple x y K ∧ pRank 2 ↥(centralizer ({x, y} : Set G)) = 4)

theorem IsV2StarStar.isV2StarTriple {x y : G} {K : Subgroup G} (h : IsV2StarStar x y K) :
    IsV2StarTriple x y K := h.1

theorem IsV2StarStar.isV2Triple {x y : G} {K : Subgroup G} (h : IsV2StarStar x y K) :
    IsV2Triple x y K := h.1.1.1.1.1

structure Th2Std (x y : G) (K T S : Subgroup G) : Prop where
  v2ss : IsV2StarStar x y K
  setup : Setup1D x K T
  y_mem : y ∈ T
  sylowS : IsSylowOf 2 S ⊤
  T_le_S : T ≤ S

@[expose] def IsDSub (K P D : Subgroup G) : Prop :=
  D ≤ P ∧ P ≤ K ∧ CFSG.IsElementaryAbelian 2 ↥D ∧ Nat.card ↥D = 4 ∧
    ∃ e : kBar K ≃* alternatingGroup (Fin 7),
      Set.ncard {i : Fin 7 | ∃ d ∈ D, ∃ hd : d ∈ K,
        ((e (QuotientGroup.mk (⟨d, hd⟩ : ↥K)) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) i ≠ i} = 6

end Std

section Table

variable {G : Type} [Group G]

inductive Th2Row
  | r1a
  | r1b
  | r2
  | r3a
  | r3b
  | r3c
  | r4a
  | r4b
  | r4c
  | r5
  deriving DecidableEq

namespace Th2Row

@[expose] def level : Th2Row → Th2Level
  | .r1a => .three
  | .r1b => .fiveHalves
  | .r2 => .fiveHalves
  | .r3a => .three
  | .r3b => .fiveHalves
  | .r3c => .fiveHalves
  | .r4a => .fiveHalves
  | .r4b => .fiveHalves
  | .r4c => .one
  | .r5 => .fiveHalves

@[expose] def holds (ρ : Th2Row) (x y : G) (K T S : Subgroup G) : Prop :=
  match ρ with
  | .r1a => HasL2Model (kBar K) (fun q => Odd q ∧ ¬ IsFM9 q) ∧
      IsConn2 (T ⊓ CxK x K) ∧ 3 ≤ pRank 2 ↥(T ⊓ CxK x K)
  | .r1b => HasL2Model (kBar K) (fun q => Odd q ∧ ¬ IsFM9 q) ∧
      (¬ IsConn2 (T ⊓ CxK x K) ∨ pRank 2 ↥(T ⊓ CxK x K) ≤ 2)
  | .r2 => HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5)
  | .r3a => Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧
      IsConn2 (T ⊓ CxK x K) ∧ 3 ≤ pRank 2 ↥(T ⊓ CxK x K)
  | .r3b => Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧ Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S
  | .r3c => Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧
      (¬ IsConn2 (T ⊓ CxK x K) ∨ pRank 2 ↥(T ⊓ CxK x K) ≤ 2) ∧
      (4 < Nat.card ↥(T ⊓ CxK x K) ∨ T = S)
  | .r4a => HasL2Model (kBar K) (fun q => q = 5) ∧ 3 ≤ pRank 2 ↥(T ⊓ CxK x K)
  | .r4b => HasL2Model (kBar K) (fun q => q = 5) ∧ pRank 2 G = 4 ∧
      pRank 2 ↥(centralizer ({x, y} : Set G)) = 4 ∧ IsUnbalancingTriple x y K
  | .r4c => HasL2Model (kBar K) (fun q => q = 5) ∧ pRank 2 G = 4 ∧
      ∀ E : Subgroup G, IsE 4 ⊤ E → IsBalancedWrt E
  | .r5 => IsL34Quotient (kBar K) ∧ CFSG.IsElementaryAbelian 2 ↥(center (kBar K)) ∧
      Nat.card ↥(center (kBar K)) ≤ 4

@[expose] def BT (ρ : Th2Row) (x : G) (K T S : Subgroup G) : Set (Subgroup G) :=
  match ρ with
  | .r1a => {B | IsSn 5 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B}
  | .r1b => {B | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B}
  | .r2 => {B | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B}
  | .r3a => {B | IsSn 5 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B ∧ ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B}
  | .r3b => {B | ∃ D, IsDSub K (T ⊓ K) D ∧
      B = ⨆ (s : G) (_ : s ∈ S), D.map (MulAut.conj s).toMonoidHom}
  | .r3c => {B | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B ∧ ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B}
  | .r4a => {B | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B}
  | .r4b => {B | IsSn 4 T B}
  | .r4c => {B | IsSn 4 T B}
  | .r5 => {B | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B}

@[expose] def Tstar (ρ : Th2Row) (x : G) (K T S : Subgroup G) : Subgroup G :=
  ⨆ B ∈ ρ.BT x K T S, B

end Th2Row

end Table

section Choice

variable {G : Type} [Group G]

structure Th2M1 (x y : G) (K T S M : Subgroup G) : Prop where
  std : Th2Std x y K T S
  terminal : IsTerminalPair 2 x K
  standard : IsStandardSubgroup K
  sylowQ : IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G))
  maximal : IsCoatom M
  le_M : normalizer (K : Set G) ≤ M

structure Th2M2 (x y : G) (K T S M : Subgroup G) (ρ : Th2Row) (B : Subgroup G) : Prop where
  std : Th2Std x y K T S
  nonterminal : ¬ IsTerminalPair 2 x K
  row : ρ.holds x y K T S
  mem : B ∈ ρ.BT x K T S
  allIsE : ∀ B' ∈ ρ.BT x K T S, IsE ρ.level.minRank T B'
  allBal : ∀ B' ∈ ρ.BT x K T S, ρ.level.IsBal B'
  theta_ne : ρ.level.theta B ≠ ⊥
  rank : pRank 2 ↥(B ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K)
  maximal : IsCoatom M
  le_M : normalizer (ρ.level.theta B : Set G) ≤ M

theorem Th2M2.isE {x y : G} {K T S M : Subgroup G} {ρ : Th2Row} {B : Subgroup G}
    (h : Th2M2 x y K T S M ρ B) : IsE ρ.level.minRank T B := h.allIsE B h.mem

theorem Th2M2.bal {x y : G} {K T S M : Subgroup G} {ρ : Th2Row} {B : Subgroup G}
    (h : Th2M2 x y K T S M ρ B) : ρ.level.IsBal B := h.allBal B h.mem

@[expose] def Th2Choice (x y : G) (K T S M : Subgroup G) : Prop :=
  Th2M1 x y K T S M ∨ ∃ (ρ : Th2Row) (B : Subgroup G), Th2M2 x y K T S M ρ B

theorem Th2Choice.std {x y : G} {K T S M : Subgroup G} (h : Th2Choice x y K T S M) :
    Th2Std x y K T S := by
  rcases h with h | ⟨ρ, B, h⟩
  · exact h.std
  · exact h.std

theorem Th2Choice.maximal {x y : G} {K T S M : Subgroup G} (h : Th2Choice x y K T S M) :
    IsCoatom M := by
  rcases h with h | ⟨ρ, B, h⟩
  · exact h.maximal
  · exact h.maximal

end Choice

section Closure

variable {G : Type} [Group G]

@[expose] def IsSubnormalIn (L M : Subgroup G) : Prop :=
  L ≤ M ∧ (L.subgroupOf M).IsSubnormal

@[expose] def IsMinSubnormalIn (K M L : Subgroup G) : Prop :=
  K ≤ L ∧ IsSubnormalIn L M ∧ ∀ J : Subgroup G, K ≤ J → J ≤ L → IsSubnormalIn J M → J = L

@[expose] def CMbar (M K : Subgroup G) : Subgroup G :=
  M ⊓ centralizerSection (K ⊔ pPrimeCoreOf 2 M) (pPrimeCoreOf 2 M)

end Closure

end CFSG.GH74.GLS
