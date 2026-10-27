module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoFactorization

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ShultStronglyClosedTI
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem pointClass_eq_internal_hull_class (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    involutionPointClass z = L.subtype '' conjugatesOf zL := by
  let D := conjugateQInvolutions Q
  let L := involutionPointHull z
  let E : Set L := {x | (x : G) ∈ D}
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  have hDclass : D = involutionPointClass z :=
    conjugateQInvolutions_eq_pointClass Q hodd hnormal z hzQ hz
  have hDL : D ⊆ (L : Set G) := fun x hx =>
    Subgroup.subset_closure (hDclass ▸ hx)
  have hEorder : ∀ x ∈ E, orderOf x = 2 := by
    intro x hx
    exact (Subgroup.orderOf_coe x).symm.trans (conjugateQInvolutions_order_two Q x hx)
  have hEconj : ∀ x ∈ E, ∀ g : L, (MulAut.conj g) x ∈ E := by
    intro x hx g
    exact conjugateQInvolutions_conj_mem Q x hx g
  have hEprod : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → Commute x y → x * y ∈ E := by
    intro x hx y hy hne hcomm
    exact conjugateQInvolutions_mul_mem Q hodd x hx y hy
      (fun heq => hne (Subtype.ext heq)) (hcomm.map L.subtype)
  let f : NormalGraph.graph E hEorder →g
      NormalGraph.graph D (conjugateQInvolutions_order_two Q) := {
    toFun := fun x => ⟨(x : L), x.property⟩
    map_rel' := by
      intro x y hadj
      refine ⟨?_, hadj.2.map L.subtype⟩
      intro heq
      apply hadj.1
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun t : CFSG.OrderReductions.InvolutionGraph.Involution G => (t : G)) heq }
  have hsurj : Function.Surjective f := by
    intro x
    exact ⟨⟨⟨x, hDL x.property⟩, x.property⟩, rfl⟩
  have hdisconnected : ¬ (NormalGraph.graph E hEorder).Preconnected := by
    intro hconnected
    exact conjugateQInvolutions_graph_disconnected Q hodd hnormal z hzQ hz
      (hconnected.map f hsurj)
  have hzE : zL ∈ E := involution_mem_conjugateQInvolutions Q z hzQ hz
  have hEclass : E = conjugatesOf zL :=
    NormalGraph.eq_conjugacy_class E hEorder hEconj hEprod hdisconnected ⟨zL, hzE⟩
  change involutionPointClass z = L.subtype '' conjugatesOf zL
  rw [← hEclass, ← hDclass]
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hDL hx⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem internal_hull_class_generates (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    Subgroup.closure (conjugatesOf zL) = (⊤ : Subgroup L) := by
  let L := involutionPointHull z
  apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype,
    ← pointClass_eq_internal_hull_class Q hodd hnormal z hzQ hz]
  rfl

theorem internal_hull_normalClosure_top (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    Subgroup.normalClosure ({zL} : Set L) = ⊤ := by
  dsimp only
  rw [← tightly_embedded_point_hull_eq_normalClosure]
  change Subgroup.closure (involutionPointClass
    (⟨z, localPointHull_distinguished_mem z⟩ : involutionPointHull z)) = ⊤
  rw [localPointHullClass_eq_conjugatesOf]
  exact internal_hull_class_generates Q hodd hnormal z hzQ hz

theorem group_eq_centralizer_mul_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    (Set.univ : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      (involutionPointHull z : Set G) := by
  let L := involutionPointHull z
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  ext g
  constructor
  · intro _
    have hconj : g⁻¹ * z * g ∈ involutionPointClass z := ⟨g, rfl⟩
    rw [pointClass_eq_internal_hull_class Q hodd hnormal z hzQ hz] at hconj
    obtain ⟨t, ht, htG⟩ := hconj
    obtain ⟨l, hl⟩ := isConj_iff.mp ht
    have hflip : (l : G) * z * (l : G)⁻¹ = g⁻¹ * z * g := by
      exact (congrArg L.subtype hl).trans htG
    have hc : g * (l : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      apply (NormalGraph.conj_eq_iff_centralizer _ _).mp
      change (g * (l : G)) * z * (g * (l : G))⁻¹ = z
      calc
        _ = g * ((l : G) * z * (l : G)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hflip]
        _ = z := by group
    exact Set.mem_mul.mpr ⟨g * (l : G), hc, (l : G)⁻¹, L.inv_mem l.property,
      mul_inv_cancel_right g (l : G)⟩
  · intro _
    trivial

end CFSG.ComponentClassification.AschbacherTightEmbedding
