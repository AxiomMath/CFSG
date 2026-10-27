module

public import CFSG.GH74.GLS.C3.Layer1.P34Stmt
public import CFSG.GH74.GLS.C3.Statements

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Concl

variable {G : Type} [Group G]

@[expose] def Prop91Concl (K M T Q : Subgroup G) : Prop :=
  (CFSG.IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4) ∧
  (∃ g : G, g ∉ M ∧ CFSG.conjugate Q g ≤ (T ⊓ K) ⊔ Q ∧ CFSG.conjugate Q g ⊓ Q = ⊥) ∧
  ((¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K') →
    ∃ q ∈ ({5, 7, 9} : Finset ℕ), HasL2Model (kBar K) (fun r => r = q)) ∧
  ((∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K') →
    HasL2Model (kBar K) (fun r => r = 5) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))

@[expose] def Lemma113Concl (x : G) (K L M T Q : Subgroup G) : Prop :=
  ¬ IsSylowOf 2 T ⊤ ∧ K = L ∧ IsTerminalPair 2 x K ∧
    ∃ n ∈ ({5, 6, 7} : Finset ℕ), Nonempty (kBar K ≃* alternatingGroup (Fin n)) ∧
      (∃ ψ : ↥M →* Equiv.Perm (Fin n), ψ.ker = (CMK M K).subgroupOf M) ∧
      (n = 5 → ∃ y ∈ T, orderOf y = 2 ∧ T = (T ⊓ K) ⊔ Q ⊔ zpowers y ∧ ∃ q ∈ Q, y * q ≠ q * y)

end Concl

@[expose] def S_prop91 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q

@[expose] def S_lemma112 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → K = L →
    (∀ q ∈ Q, ∀ t ∈ closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q) →
      (Nonempty (kBar K ≃* alternatingGroup (Fin 6)) ∧
        ∃ u ∈ T, orderOf u = 2 ∧ CFSG.GH74.GLS.C3.Layer1.P34.InducesFAutL2A7 u K) ∨
      (Nonempty (kBar K ≃* alternatingGroup (Fin 5)) ∧ (T ⊓ K) ⊔ Q = T ∧ IsSylowOf 2 T ⊤)

@[expose] def S_lemma113 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → Lemma113Concl x K L M T Q

@[expose] def S_lemma114 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → Lemma113Concl x K L M T Q →
      pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥

end CFSG.GH74.GLS
