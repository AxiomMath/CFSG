module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

theorem fourB_mul_b_one (H : FourBHyps a z) (P : FourBPair a p q) :
    ∀ t ∈ fourBSetP a z p q 1, t * (p * q) ^ 2 ∈ fourBSetP a z p q 2 := by
  obtain ⟨t₀, ht₀, -, ht₀b⟩ := fourB_exists_one H P
  exact fourB_mul_mem_of_orbit (Gxy p q) (fourBSetP a z p q 1) (fourBSetP a z p q 2)
    ((p * q) ^ 2) ((fourB_classes H P).orbit 1)
    (fourB_set_conj (a := a) (z := z) (p := p) (q := q) 2)
    (fun k hk => fourB_conj_b (p := p) (q := q) hk) t₀ ht₀ ht₀b

theorem fourB_mul_b_four (H : FourBHyps a z) (P : FourBPair a p q) :
    ∀ t ∈ fourBSetP a z p q 4, t * (p * q) ^ 2 ∈ fourBSetP a z p q 3 := by
  obtain ⟨t₀, ht₀, ht₀b⟩ := fourB_exists_four H P
  exact fourB_mul_mem_of_orbit (Gxy p q) (fourBSetP a z p q 4) (fourBSetP a z p q 3)
    ((p * q) ^ 2) ((fourB_classes H P).orbit 4)
    (fourB_set_conj (a := a) (z := z) (p := p) (q := q) 3)
    (fun k hk => fourB_conj_b (p := p) (q := q) hk) t₀ ht₀ ht₀b

theorem fourB_mul_b_six (H : FourBHyps a z) (P : FourBPair a p q) :
    ∀ t ∈ fourBSetP a z p q 6, t * (p * q) ^ 2 ∈ fourBSetP a z p q 5 := by
  obtain ⟨t₀, ht₀, ht₀b⟩ := fourB_exists_six H P
  exact fourB_mul_mem_of_orbit (Gxy p q) (fourBSetP a z p q 6) (fourBSetP a z p q 5)
    ((p * q) ^ 2) ((fourB_classes H P).orbit 6)
    (fourB_set_conj (a := a) (z := z) (p := p) (q := q) 5)
    (fun k hk => fourB_conj_b (p := p) (q := q) hk) t₀ ht₀ ht₀b

theorem fourB_one_mem_derived (H : FourBHyps a z) (P : FourBPair a p q) :
    ∀ t ∈ fourBSetP a z p q 1, t ∈ derivedOf (Gxy p q) := by
  intro t ht
  obtain ⟨t₀, ht₀, ht₀d, -⟩ := fourB_exists_one H P
  obtain ⟨k, hk, hkt⟩ := ((fourB_classes H P).orbit 1).transitive t₀ ht₀ t ht
  rw [← hkt]
  exact conj_mem_derivedOf hk ht₀d

theorem fourB_not_mem_derived (H : FourBHyps a z) (P : FourBPair a p q) {i : Fin 7} (hi : i ≠ 1)
    {t : G} (ht : t ∈ fourBSetP a z p q i) : t ∉ derivedOf (Gxy p q) := by
  intro hd
  have ht2 : orderOf t = 2 := (fourB_set_subset H P i ht).2
  have hd' := fourB_derived H P hd ht2
  have h1 : t ∈ fourBSetP a z p q 1 := by
    have hmem : (IsConj a t ∧ IsConj z (p * t)) ∧ (IsConj a t ∧ IsConj z (q * t)) :=
      ⟨⟨hd'.1, hd'.2.1⟩, ⟨hd'.1, hd'.2.2.1⟩⟩
    simpa [fourBSetP, orb2B] using hmem
  exact Set.disjoint_left.mp (fourB_set_disjoint H P i 1 hi) ht h1

end CFSG.EvenSporadicStandard.HNRecog.Section3
