module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapCentral
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {K : Type u} [Group K] [Finite K]

theorem involutions_eq_of_two_group_no_four
    (hK : IsPGroup 2 K) (hfour : ¬ TwoRankAtLeastTwo K)
    {x y : K} (hx : IsInvolution x) (hy : IsInvolution y) : x = y := by
  classical
  let : Nontrivial K := ⟨⟨x, 1, hx.ne_one⟩⟩
  have hxcard : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx.sq_eq_one hx.ne_one
  have hycard : Nat.card (Subgroup.zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy.sq_eq_one hy.ne_one
  obtain ⟨U, _, hU⟩ :=
    CFSG.BenderSuzuki.PFAppendixII.unique_order_two_subgroup_of_not_twoRank hK hfour
  have hxygroups : Subgroup.zpowers x = Subgroup.zpowers y :=
    (hU _ hxcard).trans (hU _ hycard).symm
  let x0 : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
  let y0 : Subgroup.zpowers x := ⟨y, by rw [hxygroups]; exact Subgroup.mem_zpowers y⟩
  have hx0 : x0 ≠ 1 := by
    intro h
    exact hx.ne_one (congrArg Subtype.val h)
  have hy0 : y0 ≠ 1 := by
    intro h
    exact hy.ne_one (congrArg Subtype.val h)
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers x)).mp hxcard
  exact congrArg Subtype.val ((hz x0 hx0).trans (hz y0 hy0).symm)

theorem outside_involution_in_two_subgroup
    (D P J : Subgroup K) [J.Normal]
    (hDindex : D.index = 2) (hP : IsPGroup 2 P)
    (hJodd : Odd (Nat.card J)) (hfour : ¬ TwoRankAtLeastTwo D)
    (u t : K) (hu : IsInvolution u) (ht : IsInvolution t)
    (huD : u ∈ D) (huP : u ∈ P) (htD : t ∉ D) (htP : t ∈ P)
    (htcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    {s : K} (hs : IsInvolution s) (hsP : s ∈ P) (hsD : s ∉ D) :
    s = t ∨ s = u * t := by
  let P0 : Subgroup K := P ⊓ D
  have hP0 : IsPGroup 2 P0 := hP.to_le inf_le_left
  have hP0four : ¬ TwoRankAtLeastTwo P0 := by
    intro h
    exact hfour (CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective
      (Subgroup.inclusion (show P0 ≤ D from inf_le_right))
      (Subgroup.inclusion_injective _) h)
  have hstD : s * t ∈ D := by
    exact (Subgroup.mul_mem_iff_of_index_two hDindex).mpr ⟨fun h => (hsD h).elim,
      fun h => (htD h).elim⟩
  have hstP0 : s * t ∈ P0 := ⟨P.mul_mem hsP htP, hstD⟩
  have hstcomm : Commute s t :=
    quotient_central_in_two_subgroup P J hP hJodd t htP htcentral s hsP
  have hstsq : (s * t) ^ 2 = 1 := by
    rw [hstcomm.mul_pow, hs.sq_eq_one, ht.sq_eq_one, one_mul]
  by_cases hst : s * t = 1
  · left
    calc
      s = (s * t) * t := by rw [mul_assoc, ← pow_two, ht.sq_eq_one, mul_one]
      _ = t := by rw [hst, one_mul]
  · have hu0 : IsInvolution (⟨u, huP, huD⟩ : P0) := by
      constructor
      · intro h
        exact hu.ne_one (congrArg Subtype.val h)
      · apply Subtype.ext
        exact hu.sq_eq_one
    have hst0 : IsInvolution (⟨s * t, hstP0⟩ : P0) := by
      constructor
      · intro h
        exact hst (congrArg Subtype.val h)
      · apply Subtype.ext
        exact hstsq
    have heq : s * t = u := congrArg Subtype.val
      (involutions_eq_of_two_group_no_four hP0 hP0four hst0 hu0)
    right
    calc
      s = (s * t) * t := by rw [mul_assoc, ← pow_two, ht.sq_eq_one, mul_one]
      _ = u * t := by rw [heq]

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
