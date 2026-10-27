module

public import Mathlib.GroupTheory.Index
import CFSG.GroupTheory.IndexTwoSimpleQuotient

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_le_of_relIndex_two_of_forall_relIndex_ne_two {E N₁ K N : Subgroup G}
    (hEN₁ : E ≤ N₁) (hN₁N : N₁ ≤ N) (hEK : E ≤ K) (hK : K.relIndex N = 2)
    (hQ : ∀ L : Subgroup G, E ≤ L → L ≤ N₁ → L.relIndex N₁ ≠ 2)
    (hcard : Nat.card (↥N₁ ⧸ E.subgroupOf N₁) = Nat.card (↥K ⧸ E.subgroupOf K)) :
    N₁ = K := by
  have hN₁K : N₁ ≤ K :=
    le_of_relIndex_two_of_forall_relIndex_ne_two hN₁N hK hEK hEN₁ hQ
  apply Subgroup.eq_of_le_of_card_ge hN₁K
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf N₁)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf K)
  have h3 : Nat.card (E.subgroupOf N₁) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN₁).toEquiv
  have h4 : Nat.card (E.subgroupOf K) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  rw [h3, hcard] at h1
  rw [h4] at h2
  exact (h2.trans h1.symm).le

end CFSG.GroupTheory
