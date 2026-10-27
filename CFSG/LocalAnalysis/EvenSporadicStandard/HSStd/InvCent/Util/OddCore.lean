module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem fusionOddCore_le_fusionZStar (G : Type*) [Group G] :
    fusionOddCore G ≤ fusionZStar G := by
  intro x hx
  show QuotientGroup.mk' (fusionOddCore G) x ∈ Subgroup.center _
  have h3 : QuotientGroup.mk' (fusionOddCore G) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
  rw [h3]
  exact one_mem _

theorem fusionOddCore_eq_bot_of_zstar (hZ : fusionZStar G = ⊥) : fusionOddCore G = ⊥ := by
  have h := fusionOddCore_le_fusionZStar G
  rw [hZ] at h
  exact le_bot_iff.1 h

theorem eq_one_of_central_of_zstar (hZ : fusionZStar G = ⊥) {x : G} (hx : ∀ y, y * x = x * y) :
    x = 1 := by
  have h1 : x ∈ fusionZStar G := by
    show QuotientGroup.mk' (fusionOddCore G) x ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul, hx y]
  rw [hZ, mem_bot] at h1
  exact h1

end CFSG.EvenSporadicStandard.HSStd.InvCent
