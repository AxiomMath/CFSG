module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open Subgroup

theorem mem_of_isSubnormal_of_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hG : ¬ p ^ 2 ∣ Nat.card G) {L : Subgroup G} (hL : L.IsSubnormal)
    (hpL : p ∣ Nat.card L) {x : G} (hx : orderOf x = p) : x ∈ L := by
  induction hL with
  | top => exact mem_top x
  | step H K h_le hK hN ih =>
    have hxK : x ∈ K := ih (hpL.trans (card_dvd_of_le h_le))
    have : (H.subgroupOf K).Normal := hN
    let q := QuotientGroup.mk' (H.subgroupOf K)
    have h1 : q ⟨x, hxK⟩ ^ p = 1 := by
      rw [← map_pow]
      have : (⟨x, hxK⟩ : K) ^ p = 1 := Subtype.ext (by rw [← hx]; exact pow_orderOf_eq_one x)
      rw [this, map_one]
    have h2 : q ⟨x, hxK⟩ ^ Nat.card (K ⧸ H.subgroupOf K) = 1 := pow_card_eq_one'
    have hcop : Nat.Coprime p (Nat.card (K ⧸ H.subgroupOf K)) := by
      rw [Nat.coprime_comm, ← index_eq_card]
      refine (Nat.Coprime.symm ?_)
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      apply hG
      have hK' : Nat.card K = (H.subgroupOf K).index * Nat.card H := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe h_le).toEquiv, index_mul_card]
      have : p ^ 2 ∣ Nat.card K := by
        rw [hK', pow_two]
        exact Nat.mul_dvd_mul hdvd hpL
      exact this.trans (card_subgroup_dvd_card K)
    have h3 : q ⟨x, hxK⟩ = 1 := by
      have := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rwa [hcop, pow_one] at this
    have h4 : (⟨x, hxK⟩ : K) ∈ H.subgroupOf K := (QuotientGroup.eq_one_iff _).1 h3
    exact h4

end CFSG.ComponentClassification.CatFactsSmall
