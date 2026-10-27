module

public import CFSG.GH74.GLS.C3.Statements

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

structure IsAConfig {G : Type} [Group G] [Finite G] (n : ℕ) (x : G) (K T Q S : Subgroup G) (a : G) :
    Prop where
  twoTerminal : IsTwoTerminal x K
  terminal : IsTerminalPair 2 x K
  kbar : Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin n))
  normalInC : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  hQ : Q = T ⊓ CxK x K
  sylowQ : IsSylowOf 2 Q (CxK x K)
  card_Q : Nat.card ↥Q = 4
  elemQ : IsElementaryAbelian 2 ↥Q
  sylowS : IsSylowOf 2 S ⊤
  T_lt_S : T < S
  a_mem : a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T
  cond6 : (∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) →
    ∀ u ∈ Q, u ≠ 1 → IsSylowOf 2 T (centralizer ({u} : Set G))
  noOddCore : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥
  quotientType : ∃ ψ : ↥(centralizer ({x} : Set G)) →* Equiv.Perm (Fin n),
    ψ.ker = Q.subgroupOf (centralizer ({x} : Set G)) ∧
      (ψ.range = ⊤ ∨ (n ≠ 5 ∧ ψ.range = alternatingGroup (Fin n)))
  fiveCase : n = 5 → ∃ y ∈ T, orderOf y = 2 ∧ T = (T ⊓ K) ⊔ Q ⊔ zpowers y ∧
    ∃ q ∈ Q, y * q ≠ q * y

@[expose] def AConfig (G : Type) [Group G] [Finite G] (n : ℕ) : Prop :=
  ∃ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig n x K T Q S a

@[expose] def S_layerII : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({5, 6, 7} : Finset ℕ),
    AConfig G n → IsApproxTo G (alternatingGroup (Fin (n + 4)))

end CFSG.GH74.GLS
