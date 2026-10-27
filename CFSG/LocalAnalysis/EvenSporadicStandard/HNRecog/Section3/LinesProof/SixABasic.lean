module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Coset
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem lines_sixA_setup (h : IsF5Type a z) (hF3 : Fusion3Facts a z) (hT5 : TableVFacts a z)
    {x : G} (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 ∈ orb2A a a ∧ Gxy a x ≤ Gxy a ((a * x) ^ 3) ∧
      IsShapeTwoTwoTimesA8 ↥(Gxy a ((a * x) ^ 3)) ∧ IsShapeZ2TimesSym 5 ↥(Gxy a x) := by
  have hb : (a * x) ^ 3 ∈ orb2A a a := (sixA_b_mem_orb2A h hx).1
  refine ⟨hb, fun g hg => ?_, hF3.shape_2A _ hb, hT5.shape_6A x hx⟩
  exact mem_Gxy.mpr ⟨(mem_Gxy.mp hg).1, mem_Gx.mpr (sixA_comm_b_of_mem hg).symm⟩

theorem lines_sixA_t (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hF3 : Fusion3Facts a z)
    (hPic : A8Pictures a z) (hT5 : TableVFacts a z) (h6A : SixAFacts a z) {x : G}
    (hx : x ∈ orb6A a a) :
    ∃ t ∈ Gxy a x, ∃ s ∈ derivedOf (Gxy a ((a * x) ^ 3)), t ^ 2 = 1 ∧ s ^ 2 = 1 ∧
      t = a * (a * x) ^ 3 * s ∧ IsConj z s := by
  obtain ⟨hb, hle, hX, -⟩ := lines_sixA_setup h hF3 hT5 hx
  obtain ⟨t, ht⟩ := ((h6A.classes x hx).orbit 3).nonempty
  have htK : t ∈ Gxy a x ∧ orderOf t = 2 := (h6A.classes x hx).subset 3 ht
  have ht' : t ∈ orb2A a a ∩ orb2B a z x := ht
  have hii := (h6A.case_ii x hx t ht').1
  have htb : t * (a * x) ^ 3 = (a * x) ^ 3 * t := sixA_comm_b_of_mem htK.1
  have ht2 : t ^ 2 = 1 := by rw [← htK.2]; exact pow_orderOf_eq_one t
  have haa : a * a = 1 := by rw [← pow_two]; exact sixA_a_sq h
  have hne : t ≠ a * (a * x) ^ 3 := by
    intro hteq
    have h1 : a * (t * (a * x) ^ 3) = 1 := by
      rw [hteq, show a * (a * (a * x) ^ 3 * (a * x) ^ 3) =
        (a * a) * ((a * x) ^ 3 * (a * x) ^ 3) by group, haa, one_mul, sixA_b_mul_b h hx]
    have hz := hii.1.2
    rw [h1] at hz
    have hzo := h.orderOf_z
    rw [isConj_one_left.mp hz, orderOf_one] at hzo
    exact absurd hzo (by decide)
  have hbt : IsConj a ((a * x) ^ 3 * t) := by rw [← htb]; exact hii.1.1
  obtain ⟨s, hs, hs2, hts, hsB⟩ :=
    lines_AAA h hnc (IsConj.refl a) hb hX hPic (hle htK.1) ht'.1.1 ht'.1.2 hbt hne
  exact ⟨t, htK.1, s, hs, ht2, hs2, hts, hsB⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
