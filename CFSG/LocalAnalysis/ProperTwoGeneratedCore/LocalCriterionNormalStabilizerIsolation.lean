module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizerSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizerExtension

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem local_point_normal_involution_extension_isolation
    {H M U : Subgroup G} [M.Normal] {z t : G}
    (h : InvolutionPointLocalEmbedding H z) (hgen : involutionPointHull z = ⊤)
    (hMH : M ≤ H) (hUM : U ≤ M)
    (hzc : ∀ s ∈ U, Commute z s) (htH : t ∉ H)
    (htc : ∀ s ∈ U, Commute t s) {d : G}
    (hd : d ∈ involutionPointClass z) (hdK : d ∈ U ⊔ Subgroup.zpowers z) : d = z := by
  obtain ⟨s, hs, hds | hds⟩ := commuting_involution_sup_cases U z h.distinguished_order hzc hdK
  · exact False.elim ((local_point_class_not_mem_normal_subgroup h hgen hMH hd)
      (hUM (hds ▸ hs)))
  · by_cases hs1 : s = 1
    · simpa only [hs1, one_mul] using hds
    · have hd2 := (orderOf_eq_prime_iff.mp
        (order_two_of_mem_pointClass h.distinguished_order hd)).1
      have hs2 : s ^ 2 = 1 := by
        rwa [hds, (hzc s hs).symm.mul_pow,
          (orderOf_eq_prime_iff.mp h.distinguished_order).1, mul_one] at hd2
      have hsorder : orderOf s = 2 := orderOf_eq_prime hs2 hs1
      have hescape : ¬ Subgroup.centralizer ({s} : Set G) ≤ H := by
        intro hle
        exact htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr (htc s hs)))
      have hnot := involution_point_product_not_mem h hsorder (hzc s hs).symm hescape
      exact False.elim (hnot (hds ▸ hd))

omit [Finite G] in
theorem centralizing_involution_central_in_sup (U : Subgroup G) {z : G}
    (hzc : ∀ s ∈ U, Commute z s) :
    ∀ s ∈ U ⊔ Subgroup.zpowers z, Commute z s := by
  have hC : U ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl z)
  intro s hs
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hs)).symm

end CFSG.ProperTwoGeneratedCore
