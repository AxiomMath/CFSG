module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Rank

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

structure Setup (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) : Prop where
  z_order : orderOf z = 2
  center_map : (center L).map L.subtype = zpowers z
  card_center : Nat.card (center L) = 2
  perfect : commutator L = ⊤
  quot : IsSporadic (L ⧸ center L) .Suz
  le_cent : L ≤ centralizer ({z} : Set G)
  cent_le_norm : centralizer ({z} : Set G) ≤ normalizer (L : Set G)
  relIndex_dvd : L.relIndex (centralizer ({z} : Set G)) ∣ 2

@[expose] def NoSwap {G : Type} [Group G] (z x z' : G) : Prop :=
  ∀ f : (centralizer ({z} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) ≃*
      (centralizer ({z} : Set G) ⊓ centralizer ({z'} : Set G) : Subgroup G),
    ∀ (hx : x ∈ centralizer ({z} : Set G) ⊓ centralizer ({x} : Set G))
      (hz : z ∈ centralizer ({z} : Set G) ⊓ centralizer ({x} : Set G)),
      (f ⟨x, hx⟩ : G) = z → (f ⟨z, hz⟩ : G) = z' → False

@[expose] def TwoSuzNoSwapInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
    ∀ x z' : G, x ∈ L → z' ∈ L → x ∈ centralizer ({z} : Set G) →
      z' ∈ centralizer ({z} : Set G) → orderOf x = 2 → orderOf z' = 2 → x ≠ z → z' ≠ z →
      NoSwap z x z'

@[expose] def TwoSuzNoSwapOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
    ∀ x z' : G, ¬ (x ∈ L ∧ z' ∈ L) → x ∈ centralizer ({z} : Set G) →
      z' ∈ centralizer ({z} : Set G) → orderOf x = 2 → orderOf z' = 2 → x ≠ z → z' ≠ z →
      NoSwap z x z'

end CFSG.EvenSporadicStandard.TwoSuz
