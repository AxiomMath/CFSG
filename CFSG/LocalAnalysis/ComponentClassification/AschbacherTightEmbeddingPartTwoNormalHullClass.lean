module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRankTwo

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem normal_hull_Q_twoRank (Q : Subgroup G) :
    twoRank (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))) = twoRank Q :=
  pRank_top_eq_of_equiv 2 (by decide)
    (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalClosure)

omit [Finite G] in
theorem point_hull_le_normal_hull (Q : Subgroup G) (z : G) (hzQ : z ∈ Q) :
    involutionPointHull z ≤ Subgroup.normalClosure (Q : Set G) := by
  rw [tightly_embedded_point_hull_eq_normalClosure]
  exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr hzQ)

theorem normal_hull_point_class_image (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    J.subtype '' involutionPointClass zJ = involutionPointClass z := by
  let J := Subgroup.normalClosure (Q : Set G)
  let L := involutionPointHull z
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  change J.subtype '' involutionPointClass zJ = involutionPointClass z
  apply Set.Subset.antisymm
  · rintro x ⟨a, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g : G), rfl⟩
  · intro x hx
    rw [pointClass_eq_internal_hull_class Q hodd hnormal z hzQ hz] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    let gJ : J := ⟨(g : G), point_hull_le_normal_hull Q z hzQ g.property⟩
    refine ⟨gJ * zJ * gJ⁻¹, ⟨gJ⁻¹, by
      simp only [rightConjugateElem, inv_inv]⟩, ?_⟩
    exact congrArg L.subtype hg

theorem normal_hull_point_hull_map (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    (involutionPointHull zJ).map J.subtype = involutionPointHull z := by
  dsimp only
  unfold involutionPointHull
  rw [MonoidHom.map_closure, normal_hull_point_class_image Q hodd hnormal z hzQ hz]

theorem normal_hull_point_hull_eq (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    involutionPointHull zJ = (involutionPointHull z).subgroupOf J := by
  let J := Subgroup.normalClosure (Q : Set G)
  apply Subgroup.map_injective J.subtype_injective
  rw [normal_hull_point_hull_map Q hodd hnormal z hzQ hz,
    Subgroup.map_subgroupOf_eq_of_le (point_hull_le_normal_hull Q z hzQ)]

theorem normal_hull_Q_normalClosure_top (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    Subgroup.normalClosure (Q.subgroupOf J : Set J) = ⊤ := by
  let J := Subgroup.normalClosure (Q : Set G)
  let QJ := Q.subgroupOf J
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let N := Subgroup.normalClosure (QJ : Set J)
  have hQ : Q ≤ N.map J.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalClosure : Q ≤ J)]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hL : involutionPointHull z ≤ N.map J.subtype := by
    rw [← normal_hull_point_hull_map Q hodd hnormal z hzQ hz]
    apply Subgroup.map_mono
    rw [tightly_embedded_point_hull_eq_normalClosure]
    exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr
      (show zJ ∈ QJ from hzQ))
  have hJN : J ≤ N.map J.subtype := by
    change Subgroup.normalClosure (Q : Set G) ≤ N.map J.subtype
    rw [normalClosure_eq_sup_point_hull Q hodd z hzQ hz]
    exact sup_le hQ hL
  have hmap : N.map J.subtype = J := le_antisymm (Subgroup.map_subtype_le N) hJN
  apply Subgroup.map_injective J.subtype_injective
  rw [hmap, Subgroup.map_top, Subgroup.range_subtype]

@[expose] noncomputable def normalHullPointHullEquiv (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    involutionPointHull zJ ≃* involutionPointHull z :=
  ((involutionPointHull (⟨z, Subgroup.le_normalClosure hzQ⟩ :
      Subgroup.normalClosure (Q : Set G))).equivMapOfInjective
        (Subgroup.normalClosure (Q : Set G)).subtype
        (Subgroup.normalClosure (Q : Set G)).subtype_injective).trans
    (MulEquiv.subgroupCongr (normal_hull_point_hull_map Q hodd hnormal z hzQ hz))

theorem normalHullPointHullEquiv_apply (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (x : involutionPointHull
      (⟨z, Subgroup.le_normalClosure hzQ⟩ : Subgroup.normalClosure (Q : Set G))) :
    (normalHullPointHullEquiv Q hodd hnormal z hzQ hz x : G) = ((x :
      Subgroup.normalClosure (Q : Set G)) : G) := rfl

theorem normal_hull_point_hull_perfect (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    Group.IsPerfect (involutionPointHull zJ) := by
  let : Group.IsPerfect (involutionPointHull z) :=
    point_hull_perfect_of_rank_two_Q Q hodd hnormal hrank z hzQ hz
  exact Group.IsPerfect.ofSurjective (f :=
    (normalHullPointHullEquiv Q hodd hnormal z hzQ hz).symm.toMonoidHom)
    (normalHullPointHullEquiv Q hodd hnormal z hzQ hz).symm.surjective

end CFSG.ComponentClassification.AschbacherTightEmbedding
