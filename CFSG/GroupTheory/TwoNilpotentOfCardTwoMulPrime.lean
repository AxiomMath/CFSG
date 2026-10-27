module

public import CFSG.Quasithin.Background.PSL2TwoNilpotent

public section

namespace CFSG

open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

theorem twoNilpotent_of_card_eq_two_mul_prime {A : Type*} [Group A] [Finite A] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hcard : Nat.card A = 2 * q) : TwoNilpotent A := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd : q ∣ Nat.card A := by
    rw [hcard]
    exact ⟨2, by ring⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) q hdvd
  have hMcard : Nat.card (Subgroup.zpowers a) = q := by
    rw [Nat.card_zpowers]
    exact ha
  have hMindex : (Subgroup.zpowers a).index = 2 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers a)
    rw [hMcard, hcard] at h
    have h2 : q * (Subgroup.zpowers a).index = q * 2 := by
      rw [h, Nat.mul_comm 2 q]
    exact Nat.mul_left_cancel hq.pos h2
  haveI hMn : (Subgroup.zpowers a).Normal := Subgroup.normal_of_index_eq_two hMindex
  refine ⟨Subgroup.zpowers a, hMn, ?_, fun x => ⟨1, ?_⟩⟩
  · rw [hMcard]
    exact hq.odd_of_ne_two hq2
  · simpa using Subgroup.sq_mem_of_index_two hMindex x

end CFSG
