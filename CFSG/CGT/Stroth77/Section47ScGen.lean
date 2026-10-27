module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.CGT.Stroth77

namespace Stroth47Sc

variable {G : Type*} [Group G] {X T D : Subgroup G}

theorem conj_c₂_mem_D_of_centralizes (hTX : T ≤ X) (hDT : D ≤ T)
    {c₁ c₂ : G} (hc₂ : c₂ ∈ D) (hc₂₁ : c₂ * c₂ = c₁) (hc₁ : c₁ * c₁ = 1)
    (hz : ∀ x ∈ X, x * c₁ = c₁ * x)
    (hinD : ∀ g ∈ X, g⁻¹ * c₂ * g ∈ D → g⁻¹ * c₂ * g = c₂ ∨ g⁻¹ * c₂ * g = c₂⁻¹)
    (hext : ∀ g ∈ X, g⁻¹ * c₂ * g ∈ T → ∃ k ∈ X,
      (k⁻¹ * (g⁻¹ * c₂ * g) * k = c₂ ∨ k⁻¹ * (g⁻¹ * c₂ * g) * k = c₂⁻¹) ∧
        ∀ s ∈ T, s * (g⁻¹ * c₂ * g) = (g⁻¹ * c₂ * g) * s → k⁻¹ * s * k ∈ T)
    (hsq : ∀ s ∈ T, s * c₂ = c₂ * s → s * s ∈ D)
    (hJ : ∀ y ∈ T, y ∉ D → y * c₂ = c₂ * y → y * y = c₁ →
      ∃ x ∈ D, ∃ d ∈ T, d * y = y * d ∧ x⁻¹ * y * x = y * (d * d) ∧ d * d ≠ 1 ∧ d * d ≠ c₁)
    {g : G} (hg : g ∈ X) (hgT : g⁻¹ * c₂ * g ∈ T)
    (hcomm : g⁻¹ * c₂ * g * c₂ = c₂ * (g⁻¹ * c₂ * g)) :
    g⁻¹ * c₂ * g ∈ D := by
  by_contra hyD
  set y := g⁻¹ * c₂ * g with hy
  have hyy : y * y = c₁ := by
    rw [hy]
    calc (g⁻¹ * c₂ * g) * (g⁻¹ * c₂ * g) = g⁻¹ * (c₂ * c₂) * g := by group
      _ = g⁻¹ * c₁ * g := by rw [hc₂₁]
      _ = c₁ := by
        have h := hz g hg
        calc g⁻¹ * c₁ * g = g⁻¹ * (c₁ * g) := by group
          _ = g⁻¹ * (g * c₁) := by rw [← h]
          _ = c₁ := by group
  obtain ⟨x, hxD, d, hdT, hdy, hyx, hd1, hdc⟩ := hJ y hgT hyD hcomm hyy
  obtain ⟨k, hkX, hk1, hkC⟩ := hext g hg hgT
  have hk1' : k⁻¹ * y * k = c₂ ∨ k⁻¹ * y * k = c₂⁻¹ := hk1
  have hdkT : k⁻¹ * d * k ∈ T := hkC d hdT hdy
  have hcommk : (k⁻¹ * d * k) * (k⁻¹ * y * k) =
      (k⁻¹ * y * k) * (k⁻¹ * d * k) := by
    calc (k⁻¹ * d * k) * (k⁻¹ * y * k) = k⁻¹ * (d * y) * k := by group
      _ = k⁻¹ * (y * d) * k := by rw [hdy]
      _ = (k⁻¹ * y * k) * (k⁻¹ * d * k) := by group
  have hdkc : Commute (k⁻¹ * d * k) c₂ := by
    have hc : Commute (k⁻¹ * d * k) (k⁻¹ * y * k) :=
      (commute_iff_eq _ _).mpr hcommk
    rcases hk1' with h2 | h2
    · rwa [h2] at hc
    · rw [h2] at hc
      exact Commute.inv_right_iff.mp hc
  have hdk2D : (k⁻¹ * d * k) * (k⁻¹ * d * k) ∈ D := hsq _ hdkT hdkc.eq
  have hykD : k⁻¹ * y * k ∈ D := by
    rcases hk1' with h2 | h2
    · rw [h2]; exact hc₂
    · rw [h2]; exact D.inv_mem hc₂
  have hsplit : k⁻¹ * (y * (d * d)) * k =
      (k⁻¹ * y * k) * ((k⁻¹ * d * k) * (k⁻¹ * d * k)) := by group
  have hgxkX : g * x * k ∈ X := X.mul_mem (X.mul_mem hg (hTX (hDT hxD))) hkX
  have hgxk_eq : (g * x * k)⁻¹ * c₂ * (g * x * k) = k⁻¹ * (y * (d * d)) * k := by
    calc (g * x * k)⁻¹ * c₂ * (g * x * k) =
        k⁻¹ * (x⁻¹ * (g⁻¹ * c₂ * g) * x) * k := by group
      _ = k⁻¹ * (x⁻¹ * y * x) * k := by rw [hy]
      _ = k⁻¹ * (y * (d * d)) * k := by rw [hyx]
  have hgxkD : (g * x * k)⁻¹ * c₂ * (g * x * k) ∈ D := by
    rw [hgxk_eq, hsplit]
    exact D.mul_mem hykD hdk2D
  have hfin : (k⁻¹ * y * k) * ((k⁻¹ * d * k) * (k⁻¹ * d * k)) = c₂ ∨
      (k⁻¹ * y * k) * ((k⁻¹ * d * k) * (k⁻¹ * d * k)) = c₂⁻¹ := by
    have h := hinD _ hgxkX hgxkD
    rwa [hgxk_eq, hsplit] at h
  have ha2 : (k⁻¹ * d * k) * (k⁻¹ * d * k) = 1 ∨
      (k⁻¹ * d * k) * (k⁻¹ * d * k) = c₁ := by
    have hb2 : (k⁻¹ * d * k) * (k⁻¹ * d * k) =
        (k⁻¹ * y * k)⁻¹ * ((k⁻¹ * y * k) *
          ((k⁻¹ * d * k) * (k⁻¹ * d * k))) := by group
    rcases hk1' with hb | hb <;> rcases hfin with hf | hf
    · left; rw [hb2, hf, hb]; group
    · right; rw [hb2, hf, hb]
      calc c₂⁻¹ * c₂⁻¹ = (c₂ * c₂)⁻¹ := by group
        _ = c₁⁻¹ := by rw [hc₂₁]
        _ = c₁ := inv_eq_of_mul_eq_one_right hc₁
    · right; rw [hb2, hf, hb]; simpa using hc₂₁
    · left; rw [hb2, hf, hb]; group
  have hk1c : k * c₁ * k⁻¹ = c₁ := by
    calc k * c₁ * k⁻¹ = c₁ * k * k⁻¹ := by rw [hz k hkX]
      _ = c₁ := by group
  have hconj : d * d = k * ((k⁻¹ * d * k) * (k⁻¹ * d * k)) * k⁻¹ := by group
  rcases ha2 with ha | ha
  · exact hd1 (by rw [hconj, ha]; group)
  · exact hdc (by rw [hconj, ha, hk1c])

theorem conj_c₂_eq_of_extremal (hTX : T ≤ X) (hDT : D ≤ T)
    {c₁ c₂ : G} (hc₂ : c₂ ∈ D) (hc₂₁ : c₂ * c₂ = c₁) (hc₁ : c₁ * c₁ = 1)
    (hz : ∀ x ∈ X, x * c₁ = c₁ * x)
    (hinD : ∀ g ∈ X, g⁻¹ * c₂ * g ∈ D → g⁻¹ * c₂ * g = c₂ ∨ g⁻¹ * c₂ * g = c₂⁻¹)
    (hext : ∀ g ∈ X, g⁻¹ * c₂ * g ∈ T → ∃ k ∈ X,
      (k⁻¹ * (g⁻¹ * c₂ * g) * k = c₂ ∨ k⁻¹ * (g⁻¹ * c₂ * g) * k = c₂⁻¹) ∧
        ∀ s ∈ T, s * (g⁻¹ * c₂ * g) = (g⁻¹ * c₂ * g) * s → k⁻¹ * s * k ∈ T)
    (hsq : ∀ s ∈ T, s * c₂ = c₂ * s → s * s ∈ D)
    (hJ : ∀ y ∈ T, y ∉ D → y * c₂ = c₂ * y → y * y = c₁ →
      ∃ x ∈ D, ∃ d ∈ T, d * y = y * d ∧ x⁻¹ * y * x = y * (d * d) ∧ d * d ≠ 1 ∧ d * d ≠ c₁)
    (hK : ∀ y ∈ T, y * c₂ ≠ c₂ * y → y * y = c₁ →
      ∃ x ∈ D, ∃ w ∈ T, w * y = y * w ∧ x⁻¹ * y * x = y * w ∧ w * w = 1 ∧ w ≠ 1 ∧ w ≠ c₁) :
    ∀ g ∈ X, g⁻¹ * c₂ * g ∈ T → g⁻¹ * c₂ * g = c₂ ∨ g⁻¹ * c₂ * g = c₂⁻¹ := by
  intro g hg hgT
  set y := g⁻¹ * c₂ * g with hy
  have hyy : y * y = c₁ := by
    rw [hy]
    calc (g⁻¹ * c₂ * g) * (g⁻¹ * c₂ * g) = g⁻¹ * (c₂ * c₂) * g := by group
      _ = g⁻¹ * c₁ * g := by rw [hc₂₁]
      _ = c₁ := by
        have h := hz g hg
        calc g⁻¹ * c₁ * g = g⁻¹ * (c₁ * g) := by group
          _ = g⁻¹ * (g * c₁) := by rw [← h]
          _ = c₁ := by group
  by_cases hyD : y ∈ D
  · exact hinD g hg hyD
  by_cases hcomm : y * c₂ = c₂ * y
  · exact absurd (conj_c₂_mem_D_of_centralizes hTX hDT hc₂ hc₂₁ hc₁ hz hinD hext hsq hJ hg hgT
      hcomm) hyD
  obtain ⟨x, hxD, w, hwT, hwy, hyx, _hw2, hw1, hwc₁⟩ := hK y hgT hcomm hyy
  obtain ⟨k, hkX, hk1, hkC⟩ := hext g hg hgT
  have hk1' : k⁻¹ * y * k = c₂ ∨ k⁻¹ * y * k = c₂⁻¹ := hk1
  have hwkT : k⁻¹ * w * k ∈ T := hkC w hwT hwy
  have hwkc : Commute (k⁻¹ * w * k) c₂ := by
    have hcommk : (k⁻¹ * w * k) * (k⁻¹ * y * k) =
        (k⁻¹ * y * k) * (k⁻¹ * w * k) := by
      calc (k⁻¹ * w * k) * (k⁻¹ * y * k) = k⁻¹ * (w * y) * k := by group
        _ = k⁻¹ * (y * w) * k := by rw [hwy]
        _ = (k⁻¹ * y * k) * (k⁻¹ * w * k) := by group
    have hc : Commute (k⁻¹ * w * k) (k⁻¹ * y * k) :=
      (commute_iff_eq _ _).mpr hcommk
    rcases hk1' with h2 | h2
    · rwa [h2] at hc
    · rw [h2] at hc
      exact Commute.inv_right_iff.mp hc
  have hsplit : k⁻¹ * (y * w) * k = (k⁻¹ * y * k) * (k⁻¹ * w * k) := by group
  have hgw_eq : (g * x * k)⁻¹ * c₂ * (g * x * k) = k⁻¹ * (y * w) * k := by
    calc (g * x * k)⁻¹ * c₂ * (g * x * k) =
        k⁻¹ * (x⁻¹ * (g⁻¹ * c₂ * g) * x) * k := by group
      _ = k⁻¹ * (x⁻¹ * y * x) * k := by rw [hy]
      _ = k⁻¹ * (y * w) * k := by rw [hyx]
  have hywkT : k⁻¹ * (y * w) * k ∈ T := by
    rw [hsplit]
    refine T.mul_mem ?_ hwkT
    rcases hk1' with h2 | h2
    · rw [h2]; exact hDT hc₂
    · rw [h2]; exact hDT (D.inv_mem hc₂)
  have hgxkX : g * x * k ∈ X := X.mul_mem (X.mul_mem hg (hTX (hDT hxD))) hkX
  have hgwC : (g * x * k)⁻¹ * c₂ * (g * x * k) * c₂ =
      c₂ * ((g * x * k)⁻¹ * c₂ * (g * x * k)) := by
    rw [hgw_eq, hsplit]
    have hb_c : Commute (k⁻¹ * y * k) c₂ := by
      rcases hk1' with h2 | h2
      · rw [h2]
      · rw [h2]; exact Commute.inv_left_self c₂
    exact (hb_c.mul_left hwkc).eq
  have hgxkD : (g * x * k)⁻¹ * c₂ * (g * x * k) ∈ D :=
    conj_c₂_mem_D_of_centralizes hTX hDT hc₂ hc₂₁ hc₁ hz hinD hext hsq hJ hgxkX
      (by rw [hgw_eq]; exact hywkT) hgwC
  have hfin' : (k⁻¹ * y * k) * (k⁻¹ * w * k) = c₂ ∨
      (k⁻¹ * y * k) * (k⁻¹ * w * k) = c₂⁻¹ := by
    have h := hinD _ hgxkX hgxkD
    rwa [hgw_eq, hsplit] at h
  have hwk_mem : k⁻¹ * w * k = 1 ∨ k⁻¹ * w * k = c₁ := by
    have hb2 : k⁻¹ * w * k = (k⁻¹ * y * k)⁻¹ *
        ((k⁻¹ * y * k) * (k⁻¹ * w * k)) := by group
    rcases hk1' with hb | hb <;> rcases hfin' with hf | hf
    · left; rw [hb2, hf, hb]; group
    · right; rw [hb2, hf, hb]
      calc c₂⁻¹ * c₂⁻¹ = (c₂ * c₂)⁻¹ := by group
        _ = c₁⁻¹ := by rw [hc₂₁]
        _ = c₁ := inv_eq_of_mul_eq_one_right hc₁
    · right; rw [hb2, hf, hb]; simpa using hc₂₁
    · left; rw [hb2, hf, hb]; group
  have hk1c : k * c₁ * k⁻¹ = c₁ := by
    calc k * c₁ * k⁻¹ = c₁ * k * k⁻¹ := by rw [hz k hkX]
      _ = c₁ := by group
  have hw : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
  rcases hwk_mem with h | h
  · exact (hw1 (by rw [hw, h]; group)).elim
  · exact (hwc₁ (by rw [hw, h, hk1c])).elim

end Stroth47Sc

end CFSG.CGT.Stroth77
