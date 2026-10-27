module

public import CFSG.GroupTheory.OddOrderClosure

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem odd_prime_dvd_card_oUpperTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hdvd : p ∣ Nat.card H) : p ∣ Nat.card (oddOrderClosure H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hdvd
  have hodd : Odd (orderOf (x : G)) := by
    rw [Subgroup.orderOf_coe, hx]
    exact hp.odd_of_ne_two hp2
  have hmem : (x : G) ∈ oddOrderClosure H :=
    mem_oddOrderClosure_of_mem_of_odd x.2 hodd
  have hle : Subgroup.zpowers (x : G) ≤ oddOrderClosure H := Subgroup.zpowers_le.mpr hmem
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hsub : Nat.card ((Subgroup.zpowers (x : G)).subgroupOf (oddOrderClosure H)) =
      Nat.card (Subgroup.zpowers (x : G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← hcard, ← hsub]
  exact Subgroup.card_subgroup_dvd_card ((Subgroup.zpowers (x : G)).subgroupOf
    (oddOrderClosure H))

end CFSG.GroupTheory
