module

public import CFSG.CGT.PushingUpLit.BlocksCommuteClassX
public import CFSG.CGT.PushingUpLit.BlocksCommutePrime7

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem distinct_blocks_commute (hG : IsCharacteristicP 2 G) {X Y : Subgroup G}
    (hX : IsBlockOf X) (hY : IsBlockOf Y) (hne : X ≠ Y)
    (hpq : (Nat.card (↥X ⧸ pCore 2 ↥X)).Prime → (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime →
      Nat.card (↥X ⧸ pCore 2 ↥X) = Nat.card (↥Y ⧸ pCore 2 ↥Y)) : ⁅X, Y⁆ = ⊥ := by
  rcases hX.2.quotient_type with hqX | hpX
  · exact commutator_eq_bot_of_qs hX hqX hY hne
  rcases hY.2.quotient_type with hqY | hpY
  · exact commutator_eq_bot_of_qs' hX hY hqY hne
  exact commutator_eq_bot_of_prime hG hX hY hpX rfl (hpq hpX hpY).symm hne

theorem distinct_blocks_commute_of_card_three (hG : IsCharacteristicP 2 G) {X Y : Subgroup G}
    (hX : IsBlockOf X) (hY : IsBlockOf Y) (hne : X ≠ Y)
    (hX3 : (Nat.card (↥X ⧸ pCore 2 ↥X)).Prime → Nat.card (↥X ⧸ pCore 2 ↥X) = 3)
    (hY3 : (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime → Nat.card (↥Y ⧸ pCore 2 ↥Y) = 3) :
    ⁅X, Y⁆ = ⊥ :=
  distinct_blocks_commute hG hX hY hne fun hpX hpY => (hX3 hpX).trans (hY3 hpY).symm

theorem distinct_blocks_commute_of_inClassX (hG : IsCharacteristicP 2 G) {X Y : Subgroup G}
    (hX : IsBlockInX X) (hY : IsBlockInX Y) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ :=
  distinct_blocks_commute_of_card_three hG ⟨hX.1, hX.2.1⟩ ⟨hY.1, hY.2.1⟩ hne
    (card_top_eq_three_of_inClassX hX.2) (card_top_eq_three_of_inClassX hY.2)

theorem distinct_blocks_commute_rel {K X Y : Subgroup G} (hK : IsCharacteristicP 2 ↥K)
    (hXK : X ≤ K) (hYK : Y ≤ K) (hXs : (X.subgroupOf K).IsSubnormal)
    (hYs : (Y.subgroupOf K).IsSubnormal) (hXsh : IsShortGroup ↥X) (hYsh : IsShortGroup ↥Y)
    (hne : X ≠ Y)
    (hpq : (Nat.card (↥X ⧸ pCore 2 ↥X)).Prime → (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime →
      Nat.card (↥X ⧸ pCore 2 ↥X) = Nat.card (↥Y ⧸ pCore 2 ↥Y)) : ⁅X, Y⁆ = ⊥ := by
  have hX' : IsBlockOf (X.subgroupOf K) :=
    ⟨hXs, isShortGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXK).symm hXsh⟩
  have hY' : IsBlockOf (Y.subgroupOf K) :=
    ⟨hYs, isShortGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYK).symm hYsh⟩
  have hne' : X.subgroupOf K ≠ Y.subgroupOf K := by
    intro h
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hXK, inf_eq_left.2 hYK] at h
    exact hne h
  have hcX : Nat.card (↥(X.subgroupOf K) ⧸ pCore 2 ↥(X.subgroupOf K)) =
      Nat.card (↥X ⧸ pCore 2 ↥X) :=
    (Nat.card_congr (quotTopEquiv (Subgroup.subgroupOfEquivOfLe hXK)).toEquiv)
  have hcY : Nat.card (↥(Y.subgroupOf K) ⧸ pCore 2 ↥(Y.subgroupOf K)) =
      Nat.card (↥Y ⧸ pCore 2 ↥Y) :=
    (Nat.card_congr (quotTopEquiv (Subgroup.subgroupOfEquivOfLe hYK)).toEquiv)
  have h := distinct_blocks_commute hK hX' hY' hne' (by
    rw [hcX, hcY]
    exact hpq)
  have := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXK, inf_eq_left.2 hYK,
    Subgroup.map_bot] at this

theorem distinct_blocks_commute_of_isBlockOfInX {K X Y : Subgroup G}
    (hK : IsCharacteristicP 2 ↥K) (hX : IsBlockOfInX K X) (hY : IsBlockOfInX K Y)
    (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  refine distinct_blocks_commute_rel hK hX.1 hY.1 hX.2.1 hY.2.1 hX.2.2.1 hY.2.2.1 hne ?_
  intro hpX hpY
  exact (card_top_eq_three_of_inClassX hX.2.2 hpX).trans
    (card_top_eq_three_of_inClassX hY.2.2 hpY).symm

end CFSG.CGT.PushingUpLit
