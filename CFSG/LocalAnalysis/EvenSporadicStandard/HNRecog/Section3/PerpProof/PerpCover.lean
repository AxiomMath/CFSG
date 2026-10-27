module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpRows

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private lemma perpCover_orderOf_cube_of_four {g : G} (h : orderOf g = 4) :
    orderOf (g ^ 3) = 4 := by
  rw [orderOf_pow' g (by norm_num : (3 : ℕ) ≠ 0), h]
  norm_num

private lemma perpCover_orderOf_sq_of_three {g : G} (h : orderOf g = 3) :
    orderOf (g ^ 2) = 3 := by
  rw [orderOf_pow' g (by norm_num : (2 : ℕ) ≠ 0), h]
  norm_num

private lemma perpCover_orderOf_sq_of_six {g : G} (h : orderOf g = 6) :
    orderOf (g ^ 2) = 3 := by
  rw [orderOf_pow' g (by norm_num : (2 : ℕ) ≠ 0), h]
  norm_num

private lemma perpCover_false_of_conj {a z y : G} (hI : TwoHSInterface) (h : IsF5Type a z)
    (ha : IsConj a y) (hz : IsConj z y) : False :=
  not_isConj_of_isF5Type hI h (ha.trans hz.symm)

private lemma perpCover_exists {a z b c x : G} (h : IsF5Type a z) (hT4 : TableIVFacts a z)
    (hc : c ∈ sBase a b) (hx : x ∈ orb2A a a ∩ orb2A a c) (hord : 3 ≤ orderOf (a * c)) :
    ∃ i, c ∈ sSet a z x i :=
  (hT4.partition x hx.1).cover c (perp_mem_sBase h hc hx hord)

theorem perp_mem_sSet_three (hI : TwoHSInterface) {a z b c x : G} (h : IsF5Type a z)
    (hT4 : TableIVFacts a z) (hc : c ∈ sSet a z b 3) (hx : x ∈ orb2A a a ∩ orb2A a c) :
    c ∈ sSet a z x 3 := by
  have hcb : c ∈ sBase a b := hc.1
  obtain ⟨hord, hzsq⟩ := perp_orderOf_row_three h hc
  have hord3 : 3 ≤ orderOf (a * c) := by rw [hord]; norm_num
  obtain ⟨i, hi⟩ := perpCover_exists h hT4 hcb hx hord3
  fin_cases i
  · have hi0 : c ∈ sBase a x ∧ IsConj a (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_a h hi0.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi1 : c ∈ sBase a x ∧ IsConj z (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_z h hi1.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi2 : c ∈ sBase a x ∧ (a * c) ^ 2 = x := by simpa [sSet] using hi
    have hzx : IsConj z x := by rw [← hi2.2]; exact hzsq
    exact (perpCover_false_of_conj hI h hx.1.1 hzx).elim
  · exact hi
  · have hi4 : c ∈ sBase a x ∧ orderOf (a * c) = 3 := by simpa [sSet] using hi
    have h3 : orderOf (a * c) = 3 := hi4.2
    rw [hord] at h3
    exact absurd h3 (by norm_num)
  · have hi5 : c ∈ sBase a x ∧ (a * c) ^ 3 = x := by simpa [sSet] using hi
    have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx.1.1
    have h3ord : orderOf ((a * c) ^ 3) = 2 := by rw [hi5.2, hx2]
    have h4ord : orderOf ((a * c) ^ 3) = 4 := perpCover_orderOf_cube_of_four hord
    rw [h4ord] at h3ord
    exact absurd h3ord (by norm_num)

theorem perp_mem_sSet_four (hI : TwoHSInterface) {a z b c x : G} (h : IsF5Type a z)
    (hT4 : TableIVFacts a z) (hc : c ∈ sSet a z b 4) (hx : x ∈ orb2A a a ∩ orb2A a c) :
    c ∈ sSet a z x 4 := by
  have hcb : c ∈ sBase a b := hc.1
  have hord : orderOf (a * c) = 3 := perp_orderOf_row_four hc
  have hord3 : 3 ≤ orderOf (a * c) := by rw [hord]
  obtain ⟨i, hi⟩ := perpCover_exists h hT4 hcb hx hord3
  fin_cases i
  · have hi0 : c ∈ sBase a x ∧ IsConj a (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_a h hi0.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi1 : c ∈ sBase a x ∧ IsConj z (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_z h hi1.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi2 : c ∈ sBase a x ∧ (a * c) ^ 2 = x := by simpa [sSet] using hi
    have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx.1.1
    have h2 : orderOf ((a * c) ^ 2) = 2 := by rw [hi2.2, hx2]
    have h3 : orderOf ((a * c) ^ 2) = 3 := perpCover_orderOf_sq_of_three hord
    rw [h3] at h2
    exact absurd h2 (by norm_num)
  · have hi3 : c ∈ sBase a x ∧ IsConj z ((a * c) ^ 2) := by simpa [sSet] using hi
    have h2 : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_z h hi3.2
    have h3 : orderOf ((a * c) ^ 2) = 3 := perpCover_orderOf_sq_of_three hord
    rw [h3] at h2
    exact absurd h2 (by norm_num)
  · exact hi
  · have hi5 : c ∈ sBase a x ∧ (a * c) ^ 3 = x := by simpa [sSet] using hi
    have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx.1.1
    have h1 : (a * c) ^ 3 = 1 := by simpa [hord] using pow_orderOf_eq_one (a * c)
    have hx1 : x = 1 := by rw [← hi5.2, h1]
    rw [hx1] at hx2
    rw [orderOf_one] at hx2
    exact absurd hx2 (by norm_num)

theorem perp_eq_of_row_two (hI : TwoHSInterface) {a z b c x : G} (h : IsF5Type a z)
    (hT4 : TableIVFacts a z) (hb : b ∈ orb2A a a) (hc : c ∈ sSet a z b 2)
    (hx : x ∈ orb2A a a ∩ orb2A a c) : x = b := by
  obtain ⟨hord, hsq⟩ := perp_orderOf_row_two h hb.1 hc
  have hcb : c ∈ sBase a b := hc.1
  have hord3 : 3 ≤ orderOf (a * c) := by rw [hord]; norm_num
  obtain ⟨i, hi⟩ := perpCover_exists h hT4 hcb hx hord3
  fin_cases i
  · have hi0 : c ∈ sBase a x ∧ IsConj a (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_a h hi0.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi1 : c ∈ sBase a x ∧ IsConj z (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_z h hi1.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi2 : c ∈ sBase a x ∧ (a * c) ^ 2 = x := by simpa [sSet] using hi
    rw [← hi2.2, hsq]
  · have hi3 : c ∈ sBase a x ∧ IsConj z ((a * c) ^ 2) := by simpa [sSet] using hi
    have hzb : IsConj z b := by rw [← hsq]; exact hi3.2
    exact (perpCover_false_of_conj hI h hb.1 hzb).elim
  · have hi4 : c ∈ sBase a x ∧ orderOf (a * c) = 3 := by simpa [sSet] using hi
    have h3 : orderOf (a * c) = 3 := hi4.2
    rw [hord] at h3
    exact absurd h3 (by norm_num)
  · have hi5 : c ∈ sBase a x ∧ (a * c) ^ 3 = x := by simpa [sSet] using hi
    have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx.1.1
    have h3ord : orderOf ((a * c) ^ 3) = 2 := by rw [hi5.2, hx2]
    have h4ord : orderOf ((a * c) ^ 3) = 4 := perpCover_orderOf_cube_of_four hord
    rw [h4ord] at h3ord
    exact absurd h3ord (by norm_num)

theorem perp_eq_of_row_five (hI : TwoHSInterface) {a z b c x : G} (h : IsF5Type a z)
    (hT4 : TableIVFacts a z) (hb : b ∈ orb2A a a) (hc : c ∈ sSet a z b 5)
    (hx : x ∈ orb2A a a ∩ orb2A a c) : x = b := by
  obtain ⟨hord, hcube⟩ := perp_orderOf_row_five h hb.1 hc
  have hcb : c ∈ sBase a b := hc.1
  have hord3 : 3 ≤ orderOf (a * c) := by rw [hord]; norm_num
  obtain ⟨i, hi⟩ := perpCover_exists h hT4 hcb hx hord3
  fin_cases i
  · have hi0 : c ∈ sBase a x ∧ IsConj a (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_a h hi0.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi1 : c ∈ sBase a x ∧ IsConj z (a * c) := by simpa [sSet] using hi
    have h2 : orderOf (a * c) = 2 := perp_orderOf_of_isConj_z h hi1.2
    rw [hord] at h2
    exact absurd h2 (by norm_num)
  · have hi2 : c ∈ sBase a x ∧ (a * c) ^ 2 = x := by simpa [sSet] using hi
    have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx.1.1
    have h2 : orderOf ((a * c) ^ 2) = 2 := by rw [hi2.2, hx2]
    have h3 : orderOf ((a * c) ^ 2) = 3 := perpCover_orderOf_sq_of_six hord
    rw [h3] at h2
    exact absurd h2 (by norm_num)
  · have hi3 : c ∈ sBase a x ∧ IsConj z ((a * c) ^ 2) := by simpa [sSet] using hi
    have h2 : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_z h hi3.2
    have h3 : orderOf ((a * c) ^ 2) = 3 := perpCover_orderOf_sq_of_six hord
    rw [h3] at h2
    exact absurd h2 (by norm_num)
  · have hi4 : c ∈ sBase a x ∧ orderOf (a * c) = 3 := by simpa [sSet] using hi
    have h3 : orderOf (a * c) = 3 := hi4.2
    rw [hord] at h3
    exact absurd h3 (by norm_num)
  · have hi5 : c ∈ sBase a x ∧ (a * c) ^ 3 = x := by simpa [sSet] using hi
    rw [← hi5.2, hcube]

end CFSG.EvenSporadicStandard.HNRecog.Section3
