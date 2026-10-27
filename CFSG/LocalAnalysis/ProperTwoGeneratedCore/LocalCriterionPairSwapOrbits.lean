module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapTwoGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapConjugacy
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {K : Type u} [Group K] [Finite K]

omit [Finite K] in
theorem mixed_swap_is_involution_outside
    (D : Subgroup K) (u t : K)
    (hu : IsInvolution u) (ht : IsInvolution t)
    (huD : u ∈ D) (htD : t ∉ D) (hut : Commute u t) :
    IsInvolution (u * t) ∧ u * t ∉ D := by
  have hout : u * t ∉ D := by
    intro h
    apply htD
    have hm := D.mul_mem (D.inv_mem huD) h
    simpa only [inv_mul_cancel_left] using hm
  refine ⟨⟨?_, ?_⟩, hout⟩
  · intro h
    exact hout (h ▸ D.one_mem)
  · rw [hut.mul_pow, hu.sq_eq_one, ht.sq_eq_one, one_mul]

theorem outside_involution_mem_swap_orbits
    (D J : Subgroup K) [D.Normal] [J.Normal]
    (hDindex : D.index = 2) (hJodd : Odd (Nat.card J))
    (hfour : ¬ TwoRankAtLeastTwo D)
    (u t : K) (hu : IsInvolution u) (ht : IsInvolution t)
    (huD : u ∈ D) (htD : t ∉ D) (hut : Commute u t)
    (htcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    {s : K} (hs : IsInvolution s) (hsD : s ∉ D) :
    s ∈ conjugacyWithin D t ∨ s ∈ conjugacyWithin D (u * t) := by
  obtain ⟨P, huP, htP⟩ := commuting_involutions_mem_common_sylow hu ht hut
  obtain ⟨g, hg⟩ := involution_conjugate_mem_sylow P hs
  have hconj : IsInvolution (g * s * g⁻¹) := by
    simpa only [rightConjugateElem, inv_inv] using
      (isInvolution_rightConjugateElem (g := g⁻¹) hs)
  have hconjD : g * s * g⁻¹ ∉ D := by
    intro h
    apply hsD
    have hm := (inferInstance : D.Normal).conj_mem' (g * s * g⁻¹) h g
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hm
  have htwo := outside_involution_in_two_subgroup D (P : Subgroup K) J hDindex
    P.isPGroup' hJodd hfour u t hu ht huD huP htD htP htcentral hconj hg hconjD
  have heq : ∀ z : K, g * s * g⁻¹ = z → s ∈ conjugacyWithin (⊤ : Subgroup K) z := by
    intro z hz
    refine ⟨⟨g, Subgroup.mem_top _⟩, ?_⟩
    calc
      g⁻¹ * z * g = g⁻¹ * (g * s * g⁻¹) * g := by rw [hz]
      _ = s := by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rcases htwo with heqt | hequt
  · left
    rw [← conjugacyWithin_top_eq_of_index_two D hDindex t t htD (Commute.refl t)]
    exact heq t heqt
  · right
    have hutt : Commute (u * t) t := hut.mul_left (Commute.refl t)
    rw [← conjugacyWithin_top_eq_of_index_two D hDindex t (u * t) htD hutt]
    exact heq (u * t) hequt

theorem unique_rank_one_pair_stabilizer_two_swap_orbits
    (D J : Subgroup K) [D.Normal] [J.Normal]
    (hDindex : D.index = 2) (hJodd : Odd (Nat.card J)) (hJD : J ≤ D)
    (hfour : ¬ TwoRankAtLeastTwo D)
    (u t : K) (hu : IsInvolution u) (ht : IsInvolution t)
    (huD : u ∈ D) (htD : t ∉ D) (hut : Commute u t)
    (htcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    {s : K | IsInvolution s ∧ s ∉ D} =
        conjugacyWithin D t ∪ conjugacyWithin D (u * t) ∧
      Disjoint (conjugacyWithin D t) (conjugacyWithin D (u * t)) ∧
      Nat.card (conjugacyWithin D t) =
        ((Subgroup.centralizer ({t} : Set K)).subgroupOf D).index ∧
      Nat.card (conjugacyWithin D (u * t)) =
        ((Subgroup.centralizer ({u * t} : Set K)).subgroupOf D).index := by
  have htJ : t ∉ J := fun h => htD (hJD h)
  have htI : IsInvolution t := ⟨fun h => htJ (h ▸ J.one_mem), ht.sq_eq_one⟩
  have hutI := mixed_swap_is_involution_outside D u t hu htI huD htD hut
  have hclass : ∀ z : K, IsInvolution z → z ∉ D →
      conjugacyWithin D z ⊆ {s : K | IsInvolution s ∧ s ∉ D} := by
    intro z hz hzD s hs
    obtain ⟨d, rfl⟩ := hs
    constructor
    · exact isInvolution_rightConjugateElem hz
    · intro h
      apply hzD
      have hm := (inferInstance : D.Normal).conj_mem ((d : K)⁻¹ * z * d) h (d : K)
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hm
  refine ⟨?_, swap_conjugacyWithin_disjoint D J hJodd u t hu htcentral,
    CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow.conjugacyWithin_card_eq_centralizer_index D t,
    CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow.conjugacyWithin_card_eq_centralizer_index D (u * t)⟩
  apply Set.Subset.antisymm
  · rintro s ⟨hs, hsD⟩
    exact outside_involution_mem_swap_orbits D J hDindex hJodd hfour u t hu htI
      huD htD hut htcentral hs hsD
  · exact Set.union_subset (hclass t htI htD) (hclass (u * t) hutI.1 hutI.2)

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
