module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.ElemAvoid

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_exists_QB_comm (H : GammaHyps a z) :
    ∃ v w : G, v ∈ Qz z ∧ IsConj z v ∧ v ≠ z ∧ IsConj a w ∧ w ∈ Gx z ∧ w ∈ Gx v := by
  obtain ⟨z₀, b, u, hF, hz₀, -, -, -, -, -⟩ := (H.hF1.self).rep_z
  obtain ⟨⟨-, -, -, -⟩, ⟨huB, -, -, hE5, -, -, -⟩⟩ := (H.hF2.self).reps_bu z₀ b u hF hz₀
  have hu_ord : orderOf (u : G) = 2 := H.orderOf_z huB
  have hu2 : (u : G) ^ 2 = 1 := by
    rw [← hu_ord]; exact pow_orderOf_eq_one _
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu_ord
    exact (by decide : (1 : ℕ) ≠ 2) hu_ord
  have huF : (u : G) ∈ Qz (u : G) ⊓ Gx a := ⟨self_mem_Qz hu2, u.2⟩
  obtain ⟨E, hEF, hE3, huE⟩ := exists_isElemTwo_three_avoiding hE5 huF hu1
  have hnot : ¬ (∀ t ∈ E, t ^ 2 = 1 → t ≠ 1 → IsConj a t) :=
    fun hall => (H.hCube.self).no_cube ⟨E, hE3, hall⟩
  push Not at hnot
  obtain ⟨t, htE, ht2, ht1, ht_not_conj⟩ := hnot
  have htQz : t ∈ Qz (u : G) := (hEF htE).1
  have htGx : t ∈ Gx a := (hEF htE).2
  have ht_ord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hzt : IsConj z t := ((H.hCls.self).inv_two t ht_ord).resolve_left ht_not_conj
  obtain ⟨c, hc⟩ := isConj_iff.mp huB.symm
  refine ⟨c * t * c⁻¹, c * a * c⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem := Qz_conj_mem (x := (u : G)) c htQz
    rwa [hc] at hmem
  · exact hzt.trans (isConj_iff.mpr ⟨c, rfl⟩)
  · intro hv
    have htu : t = (u : G) := mul_left_cancel (mul_right_cancel (hv.trans hc.symm))
    exact huE (htu ▸ htE)
  · exact isConj_iff.mpr ⟨c, rfl⟩
  · rw [mem_Gx, ← hc]
    calc (c * u * c⁻¹) * (c * a * c⁻¹)
        = c * (u * a) * c⁻¹ := by group
      _ = c * (a * u) * c⁻¹ := by rw [← mem_Gx.mp u.2]
      _ = (c * a * c⁻¹) * (c * u * c⁻¹) := by group
  · rw [mem_Gx]
    calc (c * t * c⁻¹) * (c * a * c⁻¹)
        = c * (t * a) * c⁻¹ := by group
      _ = c * (a * t) * c⁻¹ := by rw [← mem_Gx.mp htGx]
      _ = (c * a * c⁻¹) * (c * t * c⁻¹) := by group

end CFSG.EvenSporadicStandard.HNRecog.Section3
