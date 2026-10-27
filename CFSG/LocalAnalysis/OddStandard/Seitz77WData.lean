module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

structure WData {G : Type} [Group G] {A : Subgroup G} (d : Datum A) (V₁ : Subgroup G) where
  S : Subgroup G
  W : Subgroup G
  hS : IsSylowOf 2 S (normalizer ((V₁ ⊔ zpowers d.t : Subgroup G) : Set G))
  hWS : W ≤ S
  hWnormal : (W.subgroupOf S).Normal
  hW_elem : IsElemAbelian 2 W
  hW_card : Nat.card W = 2 ^ 8
  hV₁W : V₁ ≤ W
  hV₁_card : Nat.card V₁ = 16
  ht_mem : d.t ∈ S
  ht_not_mem : d.t ∉ W
  hCt : W ⊓ centralizer ({d.t} : Set G) = V₁
  hComm : ⁅W, zpowers d.t⁆ = V₁
  hY : S ⊓ centralizer (V₁ : Set G) = W ⊔ zpowers d.t
  hR1 : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → W.relIndex B ≤ 8
  hR2 : ∀ s ∈ S, s ∉ W ⊔ zpowers d.t → Nat.card ↥(W ⊓ centralizer ({s} : Set G)) ≤ 16

end CFSG.OddStandard.Seitz77
