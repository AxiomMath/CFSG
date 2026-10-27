module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPerfectHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem rank_two_Q_exists_commuting_involutions (Q : Subgroup G)
    (hrank : 2 ≤ twoRank Q) :
    ∃ z w : G, z ∈ Q ∧ w ∈ Q ∧ orderOf z = 2 ∧ orderOf w = 2 ∧
      z ≠ w ∧ Commute z w := by
  obtain ⟨E, hE, hcard⟩ := CFSG.ComponentClassification.Helpers.twoRank_witness Q
  have hEcard : 4 ≤ Nat.card E := by
    rw [hcard]
    exact (by norm_num : 4 = (2 : ℕ) ^ 2) ▸
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank
  have hQrank : TwoRankAtLeastTwo Q :=
    (twoRankAtLeastTwo_of_elementary_card_ge_four E hE hEcard).map_of_injective
      E.subtype E.subtype_injective
  obtain ⟨a, b, hab, hcomm⟩ := rank_two_exists_commuting_involutions (G := Q) hQrank
  refine ⟨a.val, b.val, a.val.property, b.val.property,
    (Subgroup.orderOf_coe a.val).trans a.property,
    (Subgroup.orderOf_coe b.val).trans b.property, ?_, hcomm.map Q.subtype⟩
  intro heq
  exact hab (Subtype.ext (Subtype.ext heq))

theorem involution_has_commuting_companion_of_rank_two_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    ∃ w : G, w ∈ Q ∧ orderOf w = 2 ∧ z ≠ w ∧ Commute z w := by
  obtain ⟨a, b, haQ, hbQ, ha, hb, hab, hcomm⟩ :=
    rank_two_Q_exists_commuting_involutions Q hrank
  have hzclass : z ∈ involutionPointClass a :=
    conjugateQInvolutions_eq_pointClass Q hodd hnormal a haQ ha ▸
      involution_mem_conjugateQInvolutions Q z hzQ hz
  obtain ⟨g, hg⟩ := hzclass
  let c := MulAut.conj g⁻¹
  have hca : c a = z := by
    simpa only [c, rightConjugateElem, MulAut.conj_apply, inv_inv] using hg
  have hcaQ : c a ∈ Q := hca.symm ▸ hzQ
  have hgH : g ∈ Subgroup.normalizer (Q : Set G) :=
    (involution_conjugate_mem_Q_iff Q hodd a haQ ha g).mp
      (by simpa only [c, MulAut.conj_apply, inv_inv] using hcaQ)
  have hcbQ : c b ∈ Q := by
    simpa only [c, MulAut.conj_apply, inv_inv] using
      (involution_conjugate_mem_Q_iff Q hodd b hbQ hb g).mpr hgH
  refine ⟨c b, hcbQ, (c.orderOf_eq b).trans hb, ?_, ?_⟩
  · intro heq
    exact hab (c.injective (hca.trans heq))
  · rw [← hca]
    exact hcomm.map c.toMonoidHom

theorem point_hull_perfect_of_rank_two_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    Group.IsPerfect (involutionPointHull z) := by
  obtain ⟨w, hwQ, hw, hne, hcomm⟩ :=
    involution_has_commuting_companion_of_rank_two_Q Q hodd hnormal hrank z hzQ hz
  exact point_hull_perfect_of_commuting_involutions Q hodd hnormal z w hzQ hwQ hz hw hne hcomm

end CFSG.ComponentClassification.AschbacherTightEmbedding
