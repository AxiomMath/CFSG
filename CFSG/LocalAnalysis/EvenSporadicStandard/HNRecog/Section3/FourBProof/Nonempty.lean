module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Reps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Sets
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Derived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Parity

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

theorem fourB_exists_one (H : FourBHyps a z) (P : FourBPair a p q) :
    ∃ t ∈ fourBSetP a z p q 1, t ∈ derivedOf (Gxy p q) ∧
      t * (p * q) ^ 2 ∈ fourBSetP a z p q 2 := by
  obtain ⟨t, htD, ht2⟩ := fourB_exists_derived_involution (fourB_shape_K H P)
  have htG : t ∈ Gxy p q := derivedOf_le _ htD
  have hder := fourB_derived H P htD ht2
  have htb : t * (p * q) ^ 2 = (p * q) ^ 2 * t :=
    (mul_inv_eq_iff_eq_mul).mp (fourB_conj_b htG)
  refine ⟨t, ?_, htD, ?_⟩
  · show (IsConj a t ∧ IsConj z (p * t)) ∧ (IsConj a t ∧ IsConj z (q * t))
    exact ⟨⟨hder.1, hder.2.1⟩, ⟨hder.1, hder.2.2.1⟩⟩
  · show (IsConj z (t * (p * q) ^ 2) ∧ IsConj z (p * (t * (p * q) ^ 2))) ∧
      (IsConj z (t * (p * q) ^ 2) ∧ IsConj z (q * (t * (p * q) ^ 2)))
    rw [htb]
    exact ⟨⟨hder.2.2.2.1, hder.2.2.2.2.1⟩, ⟨hder.2.2.2.1, hder.2.2.2.2.2⟩⟩

theorem fourB_exists_four (H : FourBHyps a z) (P : FourBPair a p q) :
    ∃ t ∈ fourBSetP a z p q 4, t * (p * q) ^ 2 ∈ fourBSetP a z p q 3 := by
  obtain ⟨t, htG, htD, ht2, hz, hpA, hbA, hpbA⟩ := fourB_exists_two_four H P
  have hqt : IsConj z (q * t) := by
    rcases fourB_cls_qt H P htG ht2 with h | h
    · exact False.elim (fourB_no_BAA H P htG ht2 ⟨hz, hpA, h⟩)
    · exact h
  have htb : t * (p * q) ^ 2 = (p * q) ^ 2 * t :=
    (mul_inv_eq_iff_eq_mul).mp (fourB_conj_b htG)
  have hbq : (p * q) ^ 2 ∈ orb2A q q :=
    ⟨(fourB_isConj_iff P.hq).mpr P.hb, (fourB_isConj_iff P.hq).mpr (fourB_isConj_qb H P)⟩
  have htqb : t ∈ Gxy q ((p * q) ^ 2) := fourB_Gxy_le_qb p q htG
  have hqbt : IsConj z (q * ((p * q) ^ 2 * t)) := by
    rcases fourB_coset H P.hq hbq htqb ht2 hz hbA with h | h
    · exact h.2
    · exact False.elim (fourB_not_both H h.1 hqt)
  refine ⟨t, ?_, ?_⟩
  · show (IsConj z t ∧ IsConj a (p * t)) ∧ (IsConj z t ∧ IsConj z (q * t))
    exact ⟨⟨hz, hpA⟩, ⟨hz, hqt⟩⟩
  · show (IsConj a (t * (p * q) ^ 2) ∧ IsConj a (p * (t * (p * q) ^ 2))) ∧
      (IsConj a (t * (p * q) ^ 2) ∧ IsConj z (q * (t * (p * q) ^ 2)))
    rw [htb]
    exact ⟨⟨hbA, hpbA⟩, ⟨hbA, hqbt⟩⟩

theorem fourB_exists_six (H : FourBHyps a z) (P : FourBPair a p q) :
    ∃ t ∈ fourBSetP a z p q 6, t * (p * q) ^ 2 ∈ fourBSetP a z p q 5 := by
  obtain ⟨t, ht4, ht3⟩ := fourB_exists_four H P.symm
  rw [fourBSetP_swap_four a z p q] at ht4
  rw [fourB_sq_swap H P, fourBSetP_swap_three a z p q] at ht3
  exact ⟨t, ht4, ht3⟩

theorem fourB_set_nonempty (H : FourBHyps a z) (P : FourBPair a p q) (i : Fin 7) :
    (fourBSetP a z p q i).Nonempty := by
  fin_cases i
  · exact ⟨(p * q) ^ 2, by simp [fourBSetP]⟩
  · obtain ⟨t, ht, -, -⟩ := fourB_exists_one H P
    exact ⟨t, ht⟩
  · obtain ⟨t, -, -, ht2⟩ := fourB_exists_one H P
    exact ⟨t * (p * q) ^ 2, ht2⟩
  · obtain ⟨t, -, ht3⟩ := fourB_exists_four H P
    exact ⟨t * (p * q) ^ 2, ht3⟩
  · obtain ⟨t, ht4, -⟩ := fourB_exists_four H P
    exact ⟨t, ht4⟩
  · obtain ⟨t, -, ht5⟩ := fourB_exists_six H P
    exact ⟨t * (p * q) ^ 2, ht5⟩
  · obtain ⟨t, ht6, -⟩ := fourB_exists_six H P
    exact ⟨t, ht6⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
