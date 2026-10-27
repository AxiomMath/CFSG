module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Cube.NoCube
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.ElemAvoid

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_Qz_two_B (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) :
    ∃ v : G, v ∈ Qz z ∧ IsConj z v ∧ v ≠ z := by
  obtain ⟨z₀, b, u, hF, hz₀, hz₀a, -, haQ, -, -⟩ := hF1.rep_z
  obtain ⟨⟨hbA, hbaA, -, -⟩, ⟨huB, hauB, hauQ, hE5, -, -, -⟩⟩ :=
    hF2.reps_bu z₀ b u hF hz₀
  have hu_ord : orderOf (u : G) = 2 := by
    obtain ⟨c, hc⟩ := huB
    rw [← SemiconjBy.orderOf_eq (↑c) hc, h.orderOf_z]
  have hu2 : (u : G) ^ 2 = 1 := by
    rw [← hu_ord]; exact pow_orderOf_eq_one _
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu_ord
    exact (by decide : (1 : ℕ) ≠ 2) hu_ord
  have huF : (u : G) ∈ Qz (u : G) ⊓ Gx a := ⟨self_mem_Qz hu2, u.2⟩
  obtain ⟨E, hEF, hE3, huE⟩ := exists_isElemTwo_three_avoiding hE5 huF hu1
  have hnot : ¬ (∀ t ∈ E, t ^ 2 = 1 → t ≠ 1 → IsConj a t) :=
    fun hall => no_cube_of_fusion1 hI h hF1 ⟨E, hE3, hall⟩
  push_neg at hnot
  obtain ⟨t, htE, ht2, ht1, ht_not_conj⟩ := hnot
  have htQz : t ∈ Qz (u : G) := (hEF htE).1
  have htGx : t ∈ Gx a := (hEF htE).2
  have hzt : IsConj z t := by
    rcases exists_conj_rep hF htGx ht2 ht1 with
      hta | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩
    · exact absurd (by rw [hta]) ht_not_conj
    · exact hz₀.trans (isConj_iff.mpr ⟨k, hkt⟩)
    · exact absurd (hz₀a.trans (isConj_iff.mpr ⟨k, hkt⟩)) ht_not_conj
    · exact absurd (hbA.trans (isConj_iff.mpr ⟨k, hkt⟩)) ht_not_conj
    · exact huB.trans (isConj_iff.mpr ⟨k, hkt⟩)
  obtain ⟨c, hc⟩ := isConj_iff.mp huB.symm
  refine ⟨c * t * c⁻¹, ?_, ?_, ?_⟩
  · have hmem := Qz_conj_mem (x := (u : G)) c htQz
    rwa [hc] at hmem
  · exact hzt.trans (isConj_iff.mpr ⟨c, rfl⟩)
  · intro hv
    have htu : t = (u : G) := by
      have h := hv.trans hc.symm
      exact mul_left_cancel (mul_right_cancel h)
    exact huE (htu ▸ htE)

end CFSG.EvenSporadicStandard.HNRecog.Section3
