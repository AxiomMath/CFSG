module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Local

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type} [Group G]

structure Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) : Prop where
  std : StdHyp G L
  card_center : Nat.card (center L) = 2
  quot_B : IsSporadic (L ⧸ center L) .B
  center_eq : (center L).map L.subtype = zpowers t

abbrev pair (z t : G) : Subgroup G := zpowers z ⊔ zpowers t

abbrev centZ (z : G) : Subgroup G := centralizer ({z} : Set G)

abbrev centPair (z t : G) : Subgroup G := centralizer ((pair z t : Subgroup G) : Set G)

abbrev normPair (z t : G) : Subgroup G := normalizer ((pair z t : Subgroup G) : Set G)

abbrev Rsub (z t : G) : Subgroup G := O2In (normPair z t)

abbrev Psub (z : G) : Subgroup G := O2In (centZ z)

structure CentralPair (G : Type) [Group G] [Finite G] (L : Subgroup G) (t z : G) : Prop where
  ht : t ∈ L
  hz : z ∈ L
  loc : LocalAt ↥L ⟨t, ht⟩ ⟨z, hz⟩
  loc0 : LocalR0 ↥L ⟨t, ht⟩ ⟨z, hz⟩

@[expose] def IsTwoConstrained (H : Subgroup G) : Prop :=
  H ⊓ centralizer ((O2In H : Subgroup G) : Set G) ≤ O2In H

structure Conclusion55 (G : Type) [Group G] (L : Subgroup G) (t z : G) : Prop where
  centralizer_eq : centralizer ({t} : Set G) = L
  o2K_le : O2In (centPair z t) ≤ Psub z
  extraspecial : IsExtraspecialPGroup 2 ↥(Rsub z t)
  card : Nat.card (Rsub z t) = 2 ^ 25
  le_P : Rsub z t ≤ Psub z

instance normal_zpowers_subgroupOf_centralizer (ρ : G) :
    ((zpowers ρ).subgroupOf (centralizer ({ρ} : Set G))).Normal where
  conj_mem n hn g := by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
    have hg : Commute (g : G) ρ := mem_centralizer_singleton_iff.1 g.2
    have hc : Commute (g : G) (n : G) := hk ▸ hg.zpow_right k
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ zpowers ρ
    rw [hc.mul_inv_cancel]
    exact hn

end CFSG.EvenSporadicStandard.TwoB
