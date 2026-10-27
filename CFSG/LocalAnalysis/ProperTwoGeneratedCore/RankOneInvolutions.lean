module

public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.TwoRankLowerBound.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

universe u

theorem rank_one_twoGroup_involutions_eq
    (T : Type u) [Group T] [Finite T] (hT : IsPGroup 2 T)
    (hrank : twoRank T ≤ 1) (a b : T) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    a = b := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haone : a ≠ 1 := (orderOf_eq_prime_iff.mp ha).2
  let : Nontrivial T := ⟨⟨a, 1, haone⟩⟩
  let : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center T) := hT.to_subgroup _
  have hZcard : 2 ∣ Nat.card (Subgroup.center T) :=
    hZ.card_eq_or_dvd.resolve_left (by have := Finite.one_lt_card (α := Subgroup.center T); omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZcard
  have hzorder : orderOf (z : T) = 2 := (Subgroup.orderOf_coe z).trans hz
  have haz : a = z := commuting_involutions_eq_of_twoRank_le_one T hrank
    a z ha hzorder (Subgroup.mem_center_iff.mp z.property a)
  have hbz : b = z := commuting_involutions_eq_of_twoRank_le_one T hrank
    b z hb hzorder (Subgroup.mem_center_iff.mp z.property b)
  exact haz.trans hbz.symm

variable {G : Type u} [Group G] [Finite G]

theorem rank_one_twoGroup_normalizer_fixes_involution
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hrank : pRank 2 Q ≤ 1)
    (t : G) (htQ : t ∈ Q) (ht : orderOf t = 2)
    (h : G) (hh : h ∈ Subgroup.normalizer (Q : Set G)) : h⁻¹ * t * h = t := by
  have himage : h⁻¹ * t * h ∈ Q := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set G)).inv_mem hh) t).mp htQ
  have himageorder : orderOf (h⁻¹ * t * h) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj h⁻¹).orderOf_eq t
  have hrankQ : twoRank Q ≤ 1 := by
    rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)]
    exact hrank
  exact congrArg Subtype.val
    (rank_one_twoGroup_involutions_eq Q hQ hrankQ
      ⟨h⁻¹ * t * h, himage⟩ ⟨t, htQ⟩
      ((Subgroup.orderOf_coe _).symm.trans himageorder)
      ((Subgroup.orderOf_coe _).symm.trans ht))

end CFSG.ProperTwoGeneratedCore
