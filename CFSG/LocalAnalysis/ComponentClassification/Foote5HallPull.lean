module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallGen

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_zpowers {a y : G} (h1 : a * y * a⁻¹ ∈ zpowers y)
    (h2 : a⁻¹ * y * a ∈ zpowers y) : a ∈ normalizer (zpowers y : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← conj_zpow]
    exact zpow_mem h1 i
  · intro hw
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hw
    have hw' : w = a⁻¹ * (a * w * a⁻¹) * a := by group
    rw [hw', ← hi]
    have h2' : a⁻¹ * y * a⁻¹⁻¹ ∈ zpowers y := by rwa [inv_inv]
    have := conj_zpow (a := a⁻¹) (b := y) (i := i)
    rw [inv_inv] at this
    rw [← this]
    exact zpow_mem (by rwa [inv_inv] at h2') i

variable {D : Subgroup G} {c : G}
  (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) (hk : 4 ∣ orderOf c)
  (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
    ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
include hD hk hcl

end CFSG.ComponentClassification.Foote5.HallGen
