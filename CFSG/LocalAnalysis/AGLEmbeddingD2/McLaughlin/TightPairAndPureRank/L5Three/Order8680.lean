module

public import CFSG.GroupTheory.GL52.ExcludedOrders
public import CFSG.GroupTheory.GL52.SylowSeven
public import CFSG.GroupTheory.GL52.SylowThirtyOne

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open CFSG.GroupTheory.GL52

theorem not_card_eq_8680 (H : Subgroup G52) : Nat.card H ≠ 2 ^ 3 * 5 * 7 * 31 := by
  intro hH
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hQ31 : ∀ Q : Sylow 31 H, Nat.card Q = 31 := fun Q =>
    card_sylow_of_card_eq_prime_mul (m := 280) (by rw [hH]; norm_num) (by norm_num) Q
  obtain ⟨Q31⟩ : Nonempty (Sylow 31 H) := inferInstance
  have hd31 := card_normalizer_sylow_subgroup_dvd syl31_card_sylow
    (fun P => (syl31_structure P).1) Q31 (hQ31 Q31)
  obtain ⟨hmul31, hmod31⟩ := card_sylow_mul_card_normalizer Q31
  rw [hH] at hmul31
  have hn31 : Nat.card (Sylow 31 H) = 280 := by
    set d := Nat.card (Subgroup.normalizer (Q31 : Set H))
    set n := Nat.card (Sylow 31 H)
    have hd : d ≤ 155 := Nat.le_of_dvd (by norm_num) hd31
    interval_cases d <;> omega
  have hQ7 : ∀ Q : Sylow 7 H, Nat.card Q = 7 := fun Q =>
    card_sylow_of_card_eq_prime_mul (m := 1240) (by rw [hH]; norm_num) (by norm_num) Q
  obtain ⟨Q7⟩ : Nonempty (Sylow 7 H) := inferInstance
  have hd7 := card_normalizer_sylow_subgroup_dvd syl7_card_sylow
    (fun P => (syl7_structure P).1) Q7 (hQ7 Q7)
  obtain ⟨hmul7, hmod7⟩ := card_sylow_mul_card_normalizer Q7
  rw [hH] at hmul7
  have hn7 : Nat.card (Sylow 7 H) = 1240 := by
    set d := Nat.card (Subgroup.normalizer (Q7 : Set H))
    set n := Nat.card (Sylow 7 H)
    have hd : d ≤ 126 := Nat.le_of_dvd (by norm_num) hd7
    interval_cases d <;> omega
  have h31 := ncard_orderOf_eq_prime_of_sylow hQ31
  have h7 := ncard_orderOf_eq_prime_of_sylow hQ7
  rw [hn31] at h31
  rw [hn7] at h7
  have hdisj : Disjoint {x : H | orderOf x = 31} {x : H | orderOf x = 7} := by
    rw [Set.disjoint_left]
    intro x h31' h7'
    simp only [Set.mem_setOf_eq] at h31' h7'
    rw [h31'] at h7'
    norm_num at h7'
  have hU := Set.ncard_union_eq hdisj
  have hle : ({x : H | orderOf x = 31} ∪ {x : H | orderOf x = 7}).ncard ≤ Nat.card H := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  rw [hU, h31, h7, hH] at hle
  norm_num at hle

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
