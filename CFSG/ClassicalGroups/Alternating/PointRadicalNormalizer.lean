module

public import CFSG.ClassicalGroups.Alternating.PointRadical

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem mem_pointRadical_props (hB : B.IsAlt) {v : V} {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ pointRadical B hB v) :
    (∀ x, B ((g : V →ₗ[K] V) x - x) v = 0) ∧
      ∀ x, B x v = 0 → ∃ c : K, (g : V →ₗ[K] V) x - x = c • v := by
  obtain ⟨w, c, hw, rfl⟩ := hg
  have hwv : B w v = 0 := by rw [← hB.neg_eq v w, hw, neg_zero]
  have hdiff : ∀ x, (siegel B hB v w c : V →ₗ[K] V) x - x =
      B x v • w + B x w • v + (c * B x v) • v := by
    intro x
    rw [siegel_apply hB hw]
    abel
  refine ⟨fun x => ?_, fun x hx => ⟨B x w, ?_⟩⟩
  · rw [hdiff x]
    simp [hwv, hB.self_eq_zero]
  · rw [hdiff x, hx]
    simp

end CFSG.ClassicalGroups.Alternating
