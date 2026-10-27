module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHallKernel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalHullClass

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

theorem subgroup_image_disjoint_normalizer_of_internal_disjointness
    (L : Subgroup G) (R D : Subgroup L)
    (hdisjoint : Disjoint R (Subgroup.normalizer (D : Set L))) :
    Disjoint (R.map L.subtype)
      (Subgroup.normalizer (D.map L.subtype : Set G)) := by
  apply Subgroup.disjoint_def.mpr
  intro x hxR hxN
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hxR
  have hrN : r ∈ Subgroup.normalizer (D : Set L) := by
    have hn := Subgroup.le_normalizer_comap L.subtype
      (show r ∈ (Subgroup.normalizer (D.map L.subtype : Set G)).comap L.subtype
        from hxN)
    rwa [Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at hn
  exact congrArg Subtype.val (Subgroup.disjoint_def.mp hdisjoint hr hrN)

theorem normal_factor_index_in_sup (Q L : Subgroup G) [L.Normal] :
    (L.subgroupOf (Q ⊔ L)).index = (L.subgroupOf Q).index := by
  change L.relIndex (Q ⊔ L) = L.relIndex Q
  exact Subgroup.relIndex_sup_right Q L

theorem point_hull_normalizer_normal_subgroups (Q : Subgroup G) (z : G) :
    ((involutionPointHull z).subgroupOf
      (Subgroup.normalizer (Q : Set G))).Normal ∧
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).Normal := by
  have hL : (involutionPointHull z).Normal := by
    rw [tightly_embedded_point_hull_eq_normalClosure]
    infer_instance
  exact ⟨hL.subgroupOf _, Subgroup.normal_subgroupOf_of_le_normalizer le_rfl⟩

variable [Finite G]

theorem point_hull_index_in_normalClosure_eq_Q_intersection
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    ((involutionPointHull z).subgroupOf
      (Subgroup.normalClosure (Q : Set G))).index =
      ((involutionPointHull z).subgroupOf Q).index := by
  let : (involutionPointHull z).Normal := by
    rw [tightly_embedded_point_hull_eq_normalClosure]
    infer_instance
  rw [normalClosure_eq_sup_point_hull Q hodd z hzQ hz]
  exact normal_factor_index_in_sup Q (involutionPointHull z)

theorem normal_hull_point_hull_index_eq_Q_intersection
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    (involutionPointHull zJ).index =
      ((involutionPointHull z).subgroupOf Q).index := by
  dsimp only
  rw [normal_hull_point_hull_eq Q hodd hnormal z hzQ hz]
  exact point_hull_index_in_normalClosure_eq_Q_intersection Q hodd z hzQ hz

theorem normal_hull_point_hull_odd_index_of_hall_kernel_data
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hsolv : Group.IsSolvable ((involutionPointHull z).subgroupOf
      (Subgroup.normalizer (Q : Set G))))
    (π : Set Nat.Primes)
    (D : Subgroup ((involutionPointHull z).subgroupOf
      (Subgroup.normalizer (Q : Set G))))
    (hHall : CFSG.IsHallSubgroup π D)
    (R : Subgroup (Subgroup.normalizer (Q : Set G)))
    (hcontain : ∀ x : Subgroup.normalizer (Q : Set G),
      x ∈ Q.subgroupOf (Subgroup.normalizer (Q : Set G)) →
      orderOf x = 2 → x ∈ R)
    (hdisjoint : Disjoint R
      (Subgroup.normalizer (D.map
        ((involutionPointHull z).subgroupOf
          (Subgroup.normalizer (Q : Set G))).subtype :
            Set (Subgroup.normalizer (Q : Set G))))) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    Odd (involutionPointHull zJ).index := by
  let H := Subgroup.normalizer (Q : Set G)
  let M := (involutionPointHull z).subgroupOf H
  let QH := Q.subgroupOf H
  obtain ⟨hMnormal, hQnormal⟩ := point_hull_normalizer_normal_subgroups Q z
  let : M.Normal := hMnormal
  let : QH.Normal := hQnormal
  have hoddM : Odd (M.subgroupOf QH).index :=
    odd_relative_index_of_normal_subgroup_hall_normalizer M QH M R
      hsolv le_rfl π D hHall hcontain hdisjoint
  have hindex : M.relIndex QH = (involutionPointHull z).relIndex Q :=
    Subgroup.relIndex_subgroupOf (show Q ≤ H from Subgroup.le_normalizer)
  have hoddQ : Odd ((involutionPointHull z).subgroupOf Q).index := by
    change Odd ((involutionPointHull z).relIndex Q)
    exact hindex ▸ hoddM
  dsimp only
  rw [normal_hull_point_hull_index_eq_Q_intersection Q hodd hnormal z hzQ hz]
  exact hoddQ

end CFSG.ComponentClassification.AschbacherTightEmbedding
