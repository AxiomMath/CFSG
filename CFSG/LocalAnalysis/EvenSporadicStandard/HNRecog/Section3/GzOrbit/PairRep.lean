module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_pair_reps (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) :
    ∃ z₀ u : G, ∀ x w : G, IsConj a x → IsConj z w → x * w = w * x →
      (IsConj a (x * w) ∧ ∃ g : G, g * x * g⁻¹ = a ∧ g * w * g⁻¹ = z₀) ∨
      (IsConj z (x * w) ∧ ∃ g : G, g * x * g⁻¹ = a ∧ g * w * g⁻¹ = u) := by
  obtain ⟨z₀, b, u, hF, hz₀, hz₀a, -, -, -, -⟩ := hF1.rep_z
  obtain ⟨⟨hbA, -, -, -⟩, ⟨huB, hauB, -⟩⟩ := hF2.reps_bu z₀ b u hF hz₀
  refine ⟨(z₀ : G), (u : G), ?_⟩
  intro x w hx hw hxw
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  let g₁ : G := c⁻¹
  let w' : G := g₁ * w * g₁⁻¹
  have hx1 : g₁ * x * g₁⁻¹ = a := by
    dsimp [g₁]
    rw [← hc]
    group
  have hxwconj : IsConj (x * w) (a * w') := by
    refine isConj_iff.mpr ⟨g₁, ?_⟩
    dsimp [w']
    rw [← hx1]
    group
  have hcomm : a * w' = w' * a := by
    have hconj := congrArg (fun t : G => g₁ * t * g₁⁻¹) hxw
    have h1 : g₁ * (x * w) * g₁⁻¹ = a * w' := by
      dsimp [w']
      rw [← hx1]
      group
    have h2 : g₁ * (w * x) * g₁⁻¹ = w' * a := by
      dsimp [w']
      rw [← hx1]
      group
    rw [h1, h2] at hconj
    exact hconj
  have hw' : IsConj z w' := hw.trans (isConj_iff.mpr ⟨g₁, rfl⟩)
  have hw'ord : orderOf w' = 2 := by
    obtain ⟨d, hd⟩ := isConj_iff.mp hw'
    have hord := MulEquiv.orderOf_eq (MulAut.conj d) z
    rw [MulAut.conj_apply, hd] at hord
    rw [hord, h.orderOf_z]
  have hw'2 : w' ^ 2 = 1 := by
    rw [← hw'ord, pow_orderOf_eq_one]
  have hw'1 : w' ≠ 1 := by
    intro hone
    have : orderOf w' = 1 := by rw [hone, orderOf_one]
    rw [hw'ord] at this
    exact absurd this (by norm_num : (2 : ℕ) ≠ 1)
  have hw'Gx : w' ∈ Gx a := mem_Gx.mpr hcomm
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  rcases exists_conj_rep hF hw'Gx hw'2 hw'1 with
    hwa | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩
  ·
    exfalso
    apply hnot
    rw [hwa] at hw'
    exact hw'.symm
  ·
    left
    have hkcomm : a * k = k * a := mem_Gx.mp hk
    have hka : k⁻¹ * a * k = a := by
      calc k⁻¹ * a * k = k⁻¹ * (a * k) := by rw [mul_assoc]
        _ = k⁻¹ * (k * a) := by rw [hkcomm]
        _ = (k⁻¹ * k) * a := by rw [← mul_assoc]
        _ = a := by rw [inv_mul_cancel, one_mul]
    refine ⟨?_, ⟨k⁻¹ * g₁, ?_, ?_⟩⟩
    · have hconj_az : IsConj (a * z₀) (a * w') := by
        refine isConj_iff.mpr ⟨k, ?_⟩
        rw [← hkt]
        calc k * (a * z₀) * k⁻¹
            = (k * a) * (z₀ * k⁻¹) := by group
          _ = (a * k) * (z₀ * k⁻¹) := by rw [← hkcomm]
          _ = a * (k * z₀ * k⁻¹) := by group
      exact (hz₀a.trans hconj_az).trans hxwconj.symm
    · calc (k⁻¹ * g₁) * x * (k⁻¹ * g₁)⁻¹
          = k⁻¹ * (g₁ * x * g₁⁻¹) * k := by group
        _ = k⁻¹ * a * k := by rw [hx1]
        _ = a := hka
    · calc (k⁻¹ * g₁) * w * (k⁻¹ * g₁)⁻¹
          = k⁻¹ * (g₁ * w * g₁⁻¹) * k := by group
        _ = k⁻¹ * w' * k := by dsimp [w']
        _ = k⁻¹ * (k * z₀ * k⁻¹) * k := by rw [← hkt]
        _ = z₀ := by group
  ·
    exfalso
    apply hnot
    exact (hz₀a.trans (isConj_iff.mpr ⟨k, hkt⟩)).trans hw'.symm
  ·
    exfalso
    apply hnot
    exact (hbA.trans (isConj_iff.mpr ⟨k, hkt⟩)).trans hw'.symm
  ·
    right
    have hkcomm : a * k = k * a := mem_Gx.mp hk
    have hka : k⁻¹ * a * k = a := by
      calc k⁻¹ * a * k = k⁻¹ * (a * k) := by rw [mul_assoc]
        _ = k⁻¹ * (k * a) := by rw [hkcomm]
        _ = (k⁻¹ * k) * a := by rw [← mul_assoc]
        _ = a := by rw [inv_mul_cancel, one_mul]
    refine ⟨?_, ⟨k⁻¹ * g₁, ?_, ?_⟩⟩
    · have hconj_au : IsConj (a * u) (a * w') := by
        refine isConj_iff.mpr ⟨k, ?_⟩
        rw [← hkt]
        calc k * (a * u) * k⁻¹
            = (k * a) * (u * k⁻¹) := by group
          _ = (a * k) * (u * k⁻¹) := by rw [← hkcomm]
          _ = a * (k * u * k⁻¹) := by group
      exact (hauB.trans hconj_au).trans hxwconj.symm
    · calc (k⁻¹ * g₁) * x * (k⁻¹ * g₁)⁻¹
          = k⁻¹ * (g₁ * x * g₁⁻¹) * k := by group
        _ = k⁻¹ * a * k := by rw [hx1]
        _ = a := hka
    · calc (k⁻¹ * g₁) * w * (k⁻¹ * g₁)⁻¹
          = k⁻¹ * (g₁ * w * g₁⁻¹) * k := by group
        _ = k⁻¹ * w' * k := by dsimp [w']
        _ = k⁻¹ * (k * u * k⁻¹) * k := by rw [← hkt]
        _ = u := by group

end CFSG.EvenSporadicStandard.HNRecog.Section3
