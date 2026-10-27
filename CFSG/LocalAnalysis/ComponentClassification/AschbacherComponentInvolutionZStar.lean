module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOddCoreTransport

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

variable {G : Type*} [Group G] [Finite G]

theorem weak_closed_involution_commutators_mem_oddCore (T : Sylow 2 G)
    (z : G) (hz : orderOf z = 2)
    (hzC : z ∈ Subgroup.centralizer ((T : Subgroup G) : Set G))
    (hweak : ∀ g : G, g⁻¹ * z * g ∈ (T : Subgroup G) → g⁻¹ * z * g = z) :
    ∀ g : G, g * z * g⁻¹ * z⁻¹ ∈ oddCore G := by
  have hzz : z * z = 1 := by
    simpa only [hz, pow_two] using pow_orderOf_eq_one z
  exact CFSG.ShultStronglyClosedTI.minimalLocalFailure_isolated_commutators_mem_oddCore hz
    (fun g hcomm => CFSG.Adapters.isolated_of_weakClosure T hzC hzz hweak g hcomm)

theorem central_involution_moved_in_sylow (T : Sylow 2 G)
    (z : G) (hz : orderOf z = 2)
    (hzC : z ∈ Subgroup.centralizer ((T : Subgroup G) : Set G))
    (g : G) (hnot : g * z * g⁻¹ * z⁻¹ ∉ oddCore G) :
    ∃ h : G, h⁻¹ * z * h ∈ (T : Subgroup G) ∧ h⁻¹ * z * h ≠ z := by
  by_contra hnone
  have hweak : ∀ h : G, h⁻¹ * z * h ∈ (T : Subgroup G) → h⁻¹ * z * h = z := by
    intro h hh
    by_contra hmove
    exact hnone ⟨h, hh, hmove⟩
  exact hnot (weak_closed_involution_commutators_mem_oddCore T z hz hzC hweak g)

end CFSG.ComponentClassification.AschbacherComponentInvolution
