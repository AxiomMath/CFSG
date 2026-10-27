module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRootLift
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_whole_root_as_entire_hull_point_involutions
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (U : Subgroup G)
    (hU : (U : Set G) = {1} ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G))) :
    (U : Set G) = {1} ∪ {x : G | x ∈ localInvolutionPointHull z u ∧
      x ∈ H ⊓ Subgroup.centralizer ({u} : Set G) ∧ IsInvolution x} := by
  have hclass := (original_local_hull_internal_class h u huz
    (h.local_embedding u hu huz hescape)).2.2
  rw [hU]
  ext x
  constructor
  · rintro (hxone | hx)
    · exact Or.inl hxone
    · have hxL := (Set.ext_iff.mp hclass x).mpr hx.1
      exact Or.inr ⟨hxL.1, ⟨hx.2, hx.1.2⟩,
        (orderOf_eq_prime_iff.mp hxL.2).2, (orderOf_eq_prime_iff.mp hxL.2).1⟩
  · rintro (hxone | ⟨hxL, hxHM, hx⟩)
    · exact Or.inl hxone
    · have hxorder : orderOf x = 2 := orderOf_eq_prime_iff.mpr ⟨hx.sq_eq_one, hx.ne_one⟩
      exact Or.inr ⟨(Set.ext_iff.mp hclass x).mp ⟨hxL, hxorder⟩, hxHM.1⟩

theorem original_minimal_failure_whole_root_involution_data
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let M := Subgroup.centralizer ({u} : Set G)
    let U := originalPointRoot H z u
    IsElementaryAbelian 2 U ∧ U ≤ L ∧ U ≤ H ⊓ M ∧
      (U.subgroupOf (H ⊓ M)).Normal ∧
      (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ⊓ M ∧ IsInvolution x} ∧
      4 ≤ Nat.card U ∧ ∃ a : ℕ, 2 ≤ a ∧ Nat.card U = 2 ^ a := by
  obtain ⟨a, _i, ha, _hi, _hmodel, helem, hUL, hUset, hcard, hfour,
    _hindex, hUM, hnormal, _htrans⟩ :=
    original_native_whole_point_root_of_central_oddCore h.local_datum u hu huz
      hescape hrank hcentral
  exact ⟨helem, hUL.trans inf_le_right, hUM, hnormal,
    original_whole_root_as_entire_hull_point_involutions h.local_datum u hu huz hescape
      (originalPointRoot H z u) hUset, hfour, a, ha, hcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
