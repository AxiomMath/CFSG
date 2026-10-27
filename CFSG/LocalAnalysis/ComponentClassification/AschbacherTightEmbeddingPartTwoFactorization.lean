module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoGraph
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRankOne

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ShultStronglyClosedTI
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.InvolutionFusion
open scoped Pointwise

variable {G : Type*} [Group G]

theorem tightly_embedded_point_hull_eq_normalClosure (z : G) :
    involutionPointHull z = Subgroup.normalClosure ({z} : Set G) := by
  have hclass : Group.conjugatesOfSet ({z} : Set G) = conjugatesOf z := by
    ext x
    rw [Group.mem_conjugatesOfSet_iff]
    change (∃ a, a ∈ ({z} : Set G) ∧ IsConj a x) ↔ IsConj z x
    simp only [Set.mem_singleton_iff, exists_eq_left]
  change Subgroup.closure (involutionPointClass z) =
    Subgroup.closure (Group.conjugatesOfSet ({z} : Set G))
  rw [hclass, localPointHullClass_eq_conjugatesOf]

variable [Finite G]

theorem odd_product_with_outside_conjugate (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (g : G) (hg : g ∉ Subgroup.normalizer (Q : Set G)) :
    Odd (orderOf (z * (g⁻¹ * z * g))) := by
  have hzD := involution_mem_conjugateQInvolutions Q z hzQ hz
  have hzgD := conjugateQInvolutions_conj_mem Q z hzD g⁻¹
  have hnot : ¬ (NormalGraph.graph (conjugateQInvolutions Q)
      (conjugateQInvolutions_order_two Q)).Reachable ⟨z, hzD⟩
      ⟨(MulAut.conj g⁻¹) z, hzgD⟩ := by
    intro hreach
    have hconjQ := conjugateQInvolutions_reachable_stays_in_conjugate Q hodd 1
      ⟨z, hzD⟩ ⟨(MulAut.conj g⁻¹) z, hzgD⟩
      (by simpa only [rightConjugate_one] using hzQ) hreach
    apply hg
    apply (involution_conjugate_mem_Q_iff Q hodd z hzQ hz g).mp
    simpa only [rightConjugate_one, MulAut.conj_apply, inv_inv] using hconjQ
  have h := NormalGraph.odd_product_order_of_not_reachable (conjugateQInvolutions Q)
    (conjugateQInvolutions_order_two Q) (conjugateQInvolutions_conj_mem Q)
    (conjugateQInvolutions_mul_mem Q hodd) ⟨z, hzD⟩
    ⟨(MulAut.conj g⁻¹) z, hzgD⟩ hnot
  simpa only [MulAut.conj_apply, inv_inv] using h

theorem group_normalizer_point_hull_factorization (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    ∀ g : G, ∃ h ∈ Subgroup.normalizer (Q : Set G),
      ∃ l ∈ involutionPointHull z, g = h * l := by
  intro g
  by_cases hg : g ∈ Subgroup.normalizer (Q : Set G)
  · exact ⟨g, hg, 1, (involutionPointHull z).one_mem, (mul_one g).symm⟩
  · obtain ⟨k, hk⟩ := odd_product_with_outside_conjugate Q hodd z hzQ hz g hg
    let t := g⁻¹ * z * g
    let r := z * t
    have ht : orderOf t = 2 := by
      simpa only [t, MulAut.conj_apply, inv_inv] using
        ((MulAut.conj g⁻¹).orderOf_eq z).trans hz
    let first : Involution G := ⟨z, hz⟩
    let second : Involution G := ⟨t, ht⟩
    have hflip := odd_product_conjugator_smul first second k hk
    have hflipG : r ^ k * z * (r ^ k)⁻¹ = t :=
      congrArg (fun a : Involution G => (a : G)) hflip
    have hzL : z ∈ involutionPointHull z := localPointHull_distinguished_mem z
    have htL : t ∈ involutionPointHull z := Subgroup.subset_closure ⟨g, rfl⟩
    have hrL : r ∈ involutionPointHull z := (involutionPointHull z).mul_mem hzL htL
    have hlL : r ^ k ∈ involutionPointHull z := (involutionPointHull z).pow_mem hrL k
    have hgl : g * r ^ k ∈ Subgroup.normalizer (Q : Set G) := by
      apply (Subgroup.normalizer (Q : Set G)).inv_mem_iff.mp
      apply (involution_conjugate_mem_Q_iff Q hodd z hzQ hz (g * r ^ k)⁻¹).mp
      have hfixed : ((g * r ^ k)⁻¹)⁻¹ * z * (g * r ^ k)⁻¹ = z := by
        rw [inv_inv, mul_inv_rev]
        change g * r ^ k * z * ((r ^ k)⁻¹ * g⁻¹) = z
        calc
          _ = g * (r ^ k * z * (r ^ k)⁻¹) * g⁻¹ := by group
          _ = g * t * g⁻¹ := by rw [hflipG]
          _ = z := by dsimp only [t]; group
      rw [hfixed]
      exact hzQ
    refine ⟨g * r ^ k, ?_, (r ^ k)⁻¹, (involutionPointHull z).inv_mem hlL, ?_⟩
    · exact hgl
    · exact (mul_inv_cancel_right g (r ^ k)).symm

theorem group_eq_normalizer_mul_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    (Set.univ : Set G) = (Subgroup.normalizer (Q : Set G) : Set G) *
      (involutionPointHull z : Set G) := by
  ext g
  constructor
  · intro _
    obtain ⟨h, hh, l, hl, hgl⟩ := group_normalizer_point_hull_factorization Q hodd z hzQ hz g
    exact Set.mem_mul.mpr ⟨h, hh, l, hl, hgl.symm⟩
  · intro _
    trivial

theorem normalClosure_eq_sup_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    Subgroup.normalClosure (Q : Set G) = Q ⊔ involutionPointHull z := by
  let L := involutionPointHull z
  let : L.Normal := by
    change (involutionPointHull z).Normal
    rw [tightly_embedded_point_hull_eq_normalClosure]
    infer_instance
  have hle : Subgroup.normalClosure (Q : Set G) ≤ Q ⊔ L :=
    normal_closure_le_sup_of_normalizer_factorization Q L
      (group_normalizer_point_hull_factorization Q hodd z hzQ hz)
  apply le_antisymm hle
  apply sup_le Subgroup.le_normalClosure
  change involutionPointHull z ≤ Subgroup.normalClosure (Q : Set G)
  rw [tightly_embedded_point_hull_eq_normalClosure]
  exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr hzQ)

theorem normalClosure_eq_Q_mul_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    (Subgroup.normalClosure (Q : Set G) : Set G) =
      (Q : Set G) * (involutionPointHull z : Set G) := by
  let : (involutionPointHull z).Normal := by
    rw [tightly_embedded_point_hull_eq_normalClosure]
    infer_instance
  rw [normalClosure_eq_sup_point_hull Q hodd z hzQ hz, Subgroup.mul_normal]

end CFSG.ComponentClassification.AschbacherTightEmbedding
