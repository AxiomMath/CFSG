module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

private theorem eq_one_of_isPGroup_two_of_commute_odd {G : Type*} [Group G] {A : Subgroup G}
    (hA : IsPGroup 2 A) {a b : G} (ha : a ∈ A) (hab : Commute a b) (hb : Odd (orderOf b))
    (hodd : Odd (orderOf (a * b))) : a = 1 := by
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow (p := 2) (G := A)).mp hA ⟨a, ha⟩
  simp only [Subgroup.orderOf_mk] at hk
  have hco : (orderOf a).Coprime (orderOf b) := by
    simpa using hA.orderOf_coprime hb.coprime_two_left ⟨a, ha⟩
  have hodd_a : Odd (orderOf a) :=
    (Nat.odd_mul.mp (hab.orderOf_mul_eq_mul_orderOf_of_coprime hco ▸ hodd)).1
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd_a.coprime_two_right) hk)

theorem mem_of_odd_of_mem_sup {G : Type*} [Group G] {A O : Subgroup G} (hA : IsPGroup 2 A)
    (hO : ∀ o ∈ O, Odd (orderOf o)) (hc : ∀ a ∈ A, ∀ o ∈ O, a * o = o * a) {z : G}
    (hz : z ∈ A ⊔ O) (hodd : Odd (orderOf z)) : z ∈ O := by
  have hcent : A ≤ Subgroup.centralizer (O : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    exact fun o ho => (hc a ha o ho).symm
  have hnorm : A ≤ Subgroup.normalizer (O : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (O : Set G))
  have hzmem : z ∈ ((A ⊔ O : Subgroup G) : Set G) := hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A O hnorm, Set.mem_mul] at hzmem
  obtain ⟨a, ha, o, ho, rfl⟩ := hzmem
  rw [eq_one_of_isPGroup_two_of_commute_odd hA ha (hc a ha o ho) (hO o ho) hodd, one_mul]
  exact ho

end A3

end CFSG.OddStandard.SmallF3.Omega
