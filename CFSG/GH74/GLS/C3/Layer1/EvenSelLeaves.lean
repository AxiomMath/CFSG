module

public import CFSG.GH74.GLS.C3.Layer1.EvenSetup
public import CFSG.GH74.GLS.C3.Layer1.U1aRank

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.GH74.GLS.C3.Layer1

structure EvenSelPre {G : Type} [Group G] [Finite G] (x : G) (K T Q : Subgroup G) : Prop where
  twoTerminal : IsTwoTerminal x K
  terminal : IsTerminalPair 2 x K
  isL2 : HasL2Model ↥K IsFM9
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  hQ : Q = T ⊓ CxK x K
  sylowQ : IsSylowOf 2 Q (centralizer (K : Set G))
  rankQ : 2 ≤ pRank 2 ↥Q
  sylowTM : IsSylowOf 2 T (normalizer (K : Set G))
  cent5 : ∀ u ∈ Q, (∀ t ∈ T, u * t = t * u) → orderOf u = 2 →
    IsSylowOf 2 T (centralizer ({u} : Set G))
  violation : EvenViolates x K

theorem EvenSelPre.toEvenSel {G : Type} [Group G] [Finite G] {x : G} {K T Q : Subgroup G}
    (h : EvenSelPre x K T Q)
    (five : Nonempty (↥K ≃* alternatingGroup (Fin 5)) → T = (T ⊓ K) ⊔ Q → IsSylowOf 2 T ⊤) :
    EvenSel x K T Q :=
  { twoTerminal := h.twoTerminal
    terminal := h.terminal
    isL2 := h.isL2
    sylowT := h.sylowT
    hQ := h.hQ
    sylowQ := h.sylowQ
    rankQ := h.rankQ
    sylowTM := h.sylowTM
    cent5 := h.cent5
    five := five
    violation := h.violation }

@[expose] def B_ivk_7_9_pump : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    ∀ (x' : G) (K' : Subgroup G) (x : G) (K : Subgroup G), IsILo 2 x' K' →
      HasL2Model (kBar K') (fun q => IsFM9 q ∧ ¬ (q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 17)) →
      LongPumpUp 2 x' K' x K → Nonempty (kBar K ≃* kBar K')

@[expose] def B_even_five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q : Subgroup G), EvenSelPre x K T Q →
      (∀ (x' : G) (K' T' : Subgroup G), IsTwoTerminal x' K' → EvenViolates x' K' →
        IsSylowOf 2 T' (centralizer ({x'} : Set G)) → Nat.card ↥T' ≤ Nat.card ↥T) →
      Nonempty (↥K ≃* alternatingGroup (Fin 5)) → T = (T ⊓ K) ⊔ Q → ¬ IsSylowOf 2 T ⊤ →
        EvenBCond x K

end CFSG.GH74.GLS
