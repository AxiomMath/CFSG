module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HypOne

theorem exists_conj_of_index_two {G : Type*} [Group G] {P R : Subgroup G}
    (hidx : ∀ x ∈ R, x ∉ P → ∀ y ∈ R, y ∉ P → x⁻¹ * y ∈ P) {t z : G} (hz : z ∈ R)
    (hzP : z ∉ P) (hzt : z * t = t * z) {c : G} (hc : c ∈ R) :
    ∃ g ∈ P, c * t * c⁻¹ = g * t * g⁻¹ := by
  by_cases hcP : c ∈ P
  · exact ⟨c, hcP, rfl⟩
  · refine ⟨c * z, ?_, ?_⟩
    · have h := hidx c⁻¹ (R.inv_mem hc) (fun h => hcP (by simpa using P.inv_mem h)) z hz hzP
      rwa [inv_inv] at h
    · calc c * t * c⁻¹ = c * (z * t * z⁻¹) * c⁻¹ := by rw [hzt, mul_inv_cancel_right]
        _ = c * z * t * (c * z)⁻¹ := by group

end CFSG.EvenSporadicStandard.HypOne
