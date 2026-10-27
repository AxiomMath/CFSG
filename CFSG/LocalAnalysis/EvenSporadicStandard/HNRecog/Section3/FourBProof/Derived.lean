module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Pattern
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Fig

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

theorem fourB_derived (H : FourBHyps a z) (P : FourBPair a p q) {t : G}
    (ht : t ∈ derivedOf (Gxy p q)) (ht2 : orderOf t = 2) :
    IsConj a t ∧ IsConj z (p * t) ∧ IsConj z (q * t) ∧ IsConj z ((p * q) ^ 2 * t) ∧
      IsConj z (p * ((p * q) ^ 2 * t)) ∧ IsConj z (q * ((p * q) ^ 2 * t)) := by
  have htG : t ∈ Gxy p q := derivedOf_le _ ht
  have ht_sq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have ht_ne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hbp : (p * q) ^ 2 ∈ orb2A p p := (fourB_row H P).1
  have hbq : (p * q) ^ 2 ∈ orb2A q q :=
    ⟨(fourB_isConj_iff P.hq).mpr P.hb,
      (fourB_isConj_iff P.hq).mpr (fourB_isConj_qb H P)⟩
  have ht_pb : t ∈ derivedOf (Gxy p ((p * q) ^ 2)) :=
    derivedOf_mono (fourB_Gxy_le_pb p q) ht
  have ht_qb : t ∈ derivedOf (Gxy q ((p * q) ^ 2)) :=
    derivedOf_mono (fourB_Gxy_le_qb p q) ht
  have hpf := fourB_fig H P.hp hbp ht_pb ht_sq ht_ne
  have hqf := fourB_fig H P.hq hbq ht_qb ht_sq ht_ne
  rcases hpf with hAp | hBp
  · rcases hqf with hAq | hBq
    · exact ⟨hAp.1, hAp.2.1, hAq.2.1, hAp.2.2.1, hAp.2.2.2, hAq.2.2.2⟩
    · exact False.elim (fourB_not_both H hAp.1 hBq.1)
  · rcases hqf with hAq | hBq
    · exact False.elim (fourB_not_both H hAq.1 hBp.1)
    · exact False.elim (fourB_no_BAA H P htG ht2 ⟨hBp.1, hBp.2.1, hBq.2.1⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
