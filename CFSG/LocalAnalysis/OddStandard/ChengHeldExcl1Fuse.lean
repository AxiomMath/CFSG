module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Img

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.false_of_fuse_z (hα : α ≤ 1) (c : Chart4 d α)
    (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) (hnc : ¬ IsConj d.q c.pi)
    (hidx : ∀ a ∈ d.X, a ∉ d.QS → ∀ b ∈ d.X, b ∉ d.QS → a * b ∈ d.QS)
    {z : G} (hz : z ∈ d.X) (hzQS : z ∉ d.QS) (hzq : IsConj d.q z) (hzπ : z * c.pi = c.pi * z)
    (h1 : IsConj z (z * c.pi)) (h2 : IsConj z (z * (d.q * c.pi))) : False := by
  obtain ⟨g, hg, hgX⟩ := d.exists_conj_config h hzq
  obtain ⟨hqX, hqc⟩ := d.q_mem_X h
  have hqcomm : ∀ x ∈ d.X, x * d.q = d.q * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (hqc hx)
  have hqS : d.q ∈ d.S := d.q_mem_S h
  have hqQS : d.q ∈ d.QS := mem_sup_left (d.q_mem_Q h)
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  have hπS : c.pi ∈ d.S := c.mem.1
  have hπX : c.pi ∈ d.X := d.S_le_X hπS
  have hπ2 : c.pi * c.pi = 1 := by simpa [pow_two] using c.frame.pi2
  have hπ1 : c.pi ≠ 1 := c.pi_ne_one
  have hπq : c.pi ≠ d.q := c.pi_ne_q hα h hP hQ
  have hq1 : d.q ≠ 1 := fun h1 => by
    have hord := d.q_ord
    rw [h1, orderOf_one] at hord
    omega
  have hgz : g * z * g⁻¹ = d.q := by
    calc g * z * g⁻¹ = g * (g⁻¹ * d.q * g) * g⁻¹ := by rw [hg]
      _ = d.q := by group
  have hq'X : g * d.q * g⁻¹ ∈ d.X := hgX d.q hqX (hqcomm z hz).symm
  have hπ'X : g * c.pi * g⁻¹ ∈ d.X := hgX c.pi hπX hzπ.symm
  have hq'QS : g * d.q * g⁻¹ ∉ d.QS := fun hq'QS => by
    have hq'2 : (g * d.q * g⁻¹) * (g * d.q * g⁻¹) = 1 := by
      calc (g * d.q * g⁻¹) * (g * d.q * g⁻¹) = g * (d.q * d.q) * g⁻¹ := by group
        _ = 1 := by rw [hqq]; group
    have hq'1 : g * d.q * g⁻¹ ≠ 1 := fun h1 => hq1 (by
      have h2 : g * d.q * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]; group
      exact mul_left_cancel (mul_right_cancel h2))
    have hq'q : g * d.q * g⁻¹ ≠ d.q := fun h1 => hzQS (by
      have h3 : g⁻¹ * d.q * g = d.q := by
        calc g⁻¹ * d.q * g = g⁻¹ * (g * d.q * g⁻¹) * g := by rw [h1]
          _ = d.q := by group
      rw [← hg, h3]
      exact hqQS)
    exact hnc ((isConj_iff.2 ⟨g, rfl⟩ : IsConj d.q (g * d.q * g⁻¹)).trans
      (c.involution_QS_conj_pi hα h hP hQ hc hq'QS hq'2 hq'1 hq'q))
  have key : ∀ v : G, v ∈ d.S → v * v = 1 → v ≠ 1 → v ≠ d.q → g * v * g⁻¹ ∈ d.X →
      g * v * g⁻¹ ∈ d.QS → IsConj (z * v) c.pi := by
    intro v hvS hv2 hv1 hvq hvX hvQS
    obtain ⟨w, hw⟩ : ∃ w : G, w = d.q * (g * v * g⁻¹) := ⟨_, rfl⟩
    have hwQS : w ∈ d.QS := by rw [hw]; exact d.QS.mul_mem hqQS hvQS
    have hw2 : w * w = 1 := by
      have hc' := hqcomm _ hvX
      rw [hw]
      calc d.q * (g * v * g⁻¹) * (d.q * (g * v * g⁻¹))
          = d.q * ((g * v * g⁻¹) * d.q) * (g * v * g⁻¹) := by group
        _ = d.q * (d.q * (g * v * g⁻¹)) * (g * v * g⁻¹) := by rw [hc']
        _ = (d.q * d.q) * (g * (v * v) * g⁻¹) := by group
        _ = 1 := by rw [hqq, hv2]; group
    have hw1 : w ≠ 1 := fun h1 => by
      have h3 : g * v * g⁻¹ = d.q := mul_left_cancel ((hw ▸ h1).trans hqq.symm)
      have hzv : z = v := by
        calc z = g⁻¹ * d.q * g := hg.symm
          _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [h3]
          _ = v := by group
      exact hzQS (by rw [hzv]; exact mem_sup_right hvS)
    have hwq : w ≠ d.q := fun h1 => hv1 (by
      have h3 : g * v * g⁻¹ = 1 := mul_left_cancel ((hw ▸ h1).trans (mul_one _).symm)
      have h4 : g * v * g⁻¹ = g * 1 * g⁻¹ := by rw [h3]; group
      exact mul_left_cancel (mul_right_cancel h4))
    have hwπ : IsConj w c.pi := c.involution_QS_conj_pi hα h hP hQ hc hwQS hw2 hw1 hwq
    have hzvw : IsConj (z * v) w := isConj_iff.2 ⟨g, by
      rw [hw, ← hgz]
      group⟩
    exact hzvw.trans hwπ
  by_cases hπ'QS : g * c.pi * g⁻¹ ∈ d.QS
  · exact hnc (hzq.trans (h1.trans (key c.pi hπS hπ2 hπ1 hπq hπ'X hπ'QS)))
  · have e : g * (d.q * c.pi) * g⁻¹ = (g * d.q * g⁻¹) * (g * c.pi * g⁻¹) := by group
    have hv'QS : g * (d.q * c.pi) * g⁻¹ ∈ d.QS := by
      rw [e]
      exact hidx _ hq'X hq'QS _ hπ'X hπ'QS
    have hv'X : g * (d.q * c.pi) * g⁻¹ ∈ d.X := by
      rw [e]
      exact d.X.mul_mem hq'X hπ'X
    have hqπcomm : d.q * c.pi = c.pi * d.q := (hqcomm c.pi hπX).symm
    have hv2 : (d.q * c.pi) * (d.q * c.pi) = 1 := by
      calc (d.q * c.pi) * (d.q * c.pi) = d.q * (c.pi * d.q) * c.pi := by group
        _ = d.q * (d.q * c.pi) * c.pi := by rw [← hqπcomm]
        _ = (d.q * d.q) * (c.pi * c.pi) := by group
        _ = 1 := by rw [hqq, hπ2]; group
    have hv1 : d.q * c.pi ≠ 1 := fun h1 => hπq (mul_left_cancel (h1.trans hqq.symm))
    have hvq : d.q * c.pi ≠ d.q := fun h1 => hπ1 (mul_left_cancel (h1.trans (mul_one _).symm))
    exact hnc (hzq.trans (h2.trans
      (key (d.q * c.pi) (d.S.mul_mem hqS hπS) hv2 hv1 hvq hv'X hv'QS)))

end CFSG.OddStandard.ChengHeld
