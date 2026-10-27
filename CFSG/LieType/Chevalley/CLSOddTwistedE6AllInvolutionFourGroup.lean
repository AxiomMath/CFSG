module

public import CFSG.LieType.Chevalley.CLSOddE6AllInvolutionFourGroup

public noncomputable section

namespace CFSG.LieType.Chevalley.OddTwistedE6AllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Chevalley.OddE6AllInvolution (exists_fixed_four_group_of_baseChange
  exists_four_group_inf_centralizer exists_sign_preimage isAlgebraic_zmod_algebraicClosure)

theorem mem_normalizer_of_subgroupOf_normal {G : Type*} [Group G] {H R : Subgroup G}
    (hHR : H ≤ R) (hN : (H.subgroupOf R).Normal) {y : G} (hy : y ∈ R) :
    y ∈ Subgroup.normalizer (H : Set G) := by
  have key : ∀ z ∈ R, ∀ h ∈ H, z * h * z⁻¹ ∈ H := fun z hz h hh =>
    hN.conj_mem ⟨h, hHR hh⟩ hh ⟨z, hz⟩
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨key y hy h, fun hh => ?_⟩
  have h1 := key y⁻¹ (inv_mem hy) _ hh
  have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
  rwa [e] at h1

end CFSG.LieType.Chevalley.OddTwistedE6AllInvolution
