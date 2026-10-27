module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Fig

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p b' : G}

private theorem lines_not_isConj_a_one (h : IsF5Type a z) : ¬ IsConj a 1 := by
  intro h1
  have h2 := h.orderOf_a
  rw [isConj_one_left.mp h1, orderOf_one] at h2
  exact absurd h2 (by decide)

private theorem lines_not_isConj_z_one (h : IsF5Type a z) : ¬ IsConj z 1 := by
  intro h1
  have h2 := h.orderOf_z
  rw [isConj_one_left.mp h1, orderOf_one] at h2
  exact absurd h2 (by decide)

private theorem lines_ne_one_of_isConj_a (h : IsF5Type a z) {x : G} (hx : IsConj a x) :
    x ≠ 1 :=
  fun h1 => lines_not_isConj_a_one h (h1 ▸ hx)

private theorem lines_mul_self_mul (hp2 : p ^ 2 = 1) (s : G) : p * (p * s) = s := by
  rw [← mul_assoc, ← pow_two, hp2, one_mul]

private theorem lines_b'_mul_self_mul (hb2 : b' ^ 2 = 1) (s : G) : b' * (b' * s) = s := by
  rw [← mul_assoc, ← pow_two, hb2, one_mul]

private theorem lines_mul_self_pbs (hp2 : p ^ 2 = 1) (s : G) : p * (p * b' * s) = b' * s := by
  rw [show p * (p * b' * s) = (p * p) * (b' * s) by group, ← pow_two, hp2, one_mul]

private theorem lines_pb_mul_ps (hp2 : p ^ 2 = 1) (hcomm : p * b' = b' * p) (s : G) :
    p * b' * (p * s) = b' * s := by
  rw [hcomm, show (b' * p) * (p * s) = b' * (p * (p * s)) by group]
  rw [lines_mul_self_mul hp2 s]

theorem lines_AAA (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hp : IsConj a p)
    (hb : b' ∈ orb2A p p) (hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b')) (hPic : A8Pictures p z)
    {t : G} (ht : t ∈ Gxy p b') (htA : IsConj a t) (hptA : IsConj a (p * t))
    (hbtA : IsConj a (b' * t)) (hne : t ≠ p * b') :
    ∃ s ∈ derivedOf (Gxy p b'), s ^ 2 = 1 ∧ t = p * b' * s ∧ IsConj z s := by
  obtain ⟨hp2, hb2, hcomm, -, -, -⟩ := lines_pair h hp hb
  have ht2 : t ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h htA]; exact pow_orderOf_eq_one t
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hX
  obtain ⟨s, hs, hs2, hcase⟩ := lines_decomp h hp hb hX ht ht2
  have hcase' := hcase
  have hs1 : s ≠ 1 := by
    intro h1
    rcases hcase' with h' | h' | h' | h'
    · exact lines_ne_one_of_isConj_a h htA (h'.trans h1)
    · apply lines_not_isConj_a_one h
      have hpt : p * t = 1 := by rw [h', lines_mul_self_mul hp2 s, h1]
      rwa [hpt] at hptA
    · apply lines_not_isConj_a_one h
      have hbt : b' * t = 1 := by rw [h', lines_b'_mul_self_mul hb2 s, h1]
      rwa [hbt] at hbtA
    · exact hne (h'.trans (by rw [h1, mul_one]))
  rcases lines_fig hp hb hPic φ hs hs2 hs1 with hA | hB
  · rcases hcase with h' | h' | h' | h'
    · have hpt : IsConj a (p * s) := by rwa [h'] at hptA
      exact absurd (hpt.trans hA.2.2.1.symm) hnc
    · have ht' : IsConj a (p * s) := by rwa [h'] at htA
      exact absurd (ht'.trans hA.2.2.1.symm) hnc
    · have ht' : IsConj a (b' * s) := by rwa [h'] at htA
      exact absurd (ht'.trans hA.2.2.2.1.symm) hnc
    · have ht' : IsConj a (p * b' * s) := by rwa [h'] at htA
      exact absurd (ht'.trans hA.2.2.2.2.symm) hnc
  · rcases hcase with h' | h' | h' | h'
    · have ht' : IsConj a s := by rwa [h'] at htA
      exact absurd (ht'.trans hB.2.1.symm) hnc
    · have hpt : IsConj a s := by rwa [h', lines_mul_self_mul hp2 s] at hptA
      exact absurd (hpt.trans hB.2.1.symm) hnc
    · have hbt : IsConj a s := by rwa [h', lines_b'_mul_self_mul hb2 s] at hbtA
      exact absurd (hbt.trans hB.2.1.symm) hnc
    · exact ⟨s, hs, hs2, h', hB.2.1⟩

theorem lines_coset (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hp : IsConj a p)
    (hb : b' ∈ orb2A p p) (hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b')) (hPic : A8Pictures p z)
    {w : G} (hw : w ∈ Gxy p b') (hwB : IsConj z w) (hpw : IsConj a (p * w))
    (hpbw : IsConj a (p * b' * w)) : IsConj a (b' * w) := by
  obtain ⟨hp2, hb2, hcomm, -, -, -⟩ := lines_pair h hp hb
  have hw2 : w ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_z h hwB]; exact pow_orderOf_eq_one w
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hX
  obtain ⟨s, hs, hs2, hcase⟩ := lines_decomp h hp hb hX hw hw2
  have hcase' := hcase
  have hs1 : s ≠ 1 := by
    intro h1
    rcases hcase' with h' | h' | h' | h'
    · have hz : IsConj z (1 : G) := by rwa [h', h1] at hwB
      exact lines_not_isConj_z_one h hz
    · apply hnc
      have hz : IsConj z p := by rwa [h', h1, mul_one] at hwB
      exact hp.trans hz.symm
    · apply hnc
      have hz : IsConj z b' := by rwa [h', h1, mul_one] at hwB
      exact (hp.trans hb.1).trans hz.symm
    · apply hnc
      have hz : IsConj z (p * b') := by rwa [h', h1, mul_one] at hwB
      exact (hp.trans hb.2).trans hz.symm
  rcases lines_fig hp hb hPic φ hs hs2 hs1 with hA | hB
  · rcases hcase with h' | h' | h' | h'
    · have hz : IsConj z s := by rwa [h'] at hwB
      exact absurd (hA.2.1.trans hz.symm) hnc
    · have hpb : IsConj a (b' * s) := by
        rwa [h', lines_pb_mul_ps hp2 hcomm s] at hpbw
      exact absurd (hpb.trans hA.2.2.2.1.symm) hnc
    · have hp' : IsConj a (p * b' * s) := by rwa [h', ← mul_assoc] at hpw
      exact absurd (hp'.trans hA.2.2.2.2.symm) hnc
    · have hp' : IsConj a (b' * s) := by rwa [h', lines_mul_self_pbs hp2 s] at hpw
      exact absurd (hp'.trans hA.2.2.2.1.symm) hnc
  · rcases hcase with h' | h' | h' | h'
    · rw [h']; exact hB.2.2.2.1
    · have hp' : IsConj a s := by rwa [h', lines_mul_self_mul hp2 s] at hpw
      exact absurd (hp'.trans hB.2.1.symm) hnc
    · have ha : IsConj a w := by rw [h']; exact hB.2.2.2.1
      exact absurd (ha.trans hwB.symm) hnc
    · have ha : IsConj a w := by rw [h']; exact hB.2.2.2.2
      exact absurd (ha.trans hwB.symm) hnc

end CFSG.EvenSporadicStandard.HNRecog.Section3
