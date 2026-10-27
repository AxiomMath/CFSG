module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def properHull (Y : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.closure (conjugacyWithin Y z)

theorem internal_pointClass_image (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    Y.subtype '' involutionPointClass (⟨z, hzY⟩ : Y) = conjugacyWithin Y z := by
  ext x
  constructor
  · rintro ⟨t, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨rightConjugateElem (⟨z, hzY⟩ : Y) y, ⟨y, rfl⟩, rfl⟩

theorem internal_hull_map (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    (involutionPointHull (⟨z, hzY⟩ : Y)).map Y.subtype = properHull Y z := by
  rw [involutionPointHull, MonoidHom.map_closure, internal_pointClass_image]
  rfl

theorem properHull_le (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    properHull Y z ≤ Y := by
  rw [← internal_hull_map Y hzY]
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem distinguished_mem_properHull (Y : Subgroup G) (z : G) :
    z ∈ properHull Y z := by
  apply Subgroup.subset_closure
  exact ⟨1, by simp⟩

@[expose] def properHullEquiv (Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    involutionPointHull (⟨z, hzY⟩ : Y) ≃* properHull Y z :=
  ((involutionPointHull (⟨z, hzY⟩ : Y)).equivMapOfInjective
    Y.subtype Y.subtype_injective).trans (MulEquiv.subgroupCongr (internal_hull_map Y hzY))

theorem properHullEquiv_coe (Y : Subgroup G) {z : G} (hzY : z ∈ Y)
    (x : involutionPointHull (⟨z, hzY⟩ : Y)) :
    (properHullEquiv Y hzY x : G) = (x.val : G) := rfl

theorem properHullEquiv_point_map (H Y : Subgroup G) {z : G} (hzY : z ∈ Y) :
    ((H.subgroupOf Y).subgroupOf (involutionPointHull (⟨z, hzY⟩ : Y))).map
      (properHullEquiv Y hzY).toMonoidHom = H.subgroupOf (properHull Y z) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    obtain ⟨a, rfl⟩ := (properHullEquiv Y hzY).surjective x
    exact ⟨a, hx, rfl⟩

theorem proper_subgroup_local_datum [Finite G] {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨z, hzY⟩ : Y) ∧
      InvolutionPointCentralSylow (⟨z, hzY⟩ : Y) := by
  obtain ⟨hlocal, hcentral⟩ :=
    involution_point_subgroup_inheritance h.local_datum Y hzY hescape
  exact ⟨hlocal, hcentral h.central_sylow⟩

theorem proper_subgroup_card_lt [Finite G] {Y : Subgroup G} (hY : Y < ⊤) :
    Nat.card Y < Nat.card G := by
  simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt hY

theorem properHull_card_lt [Finite G] {Y : Subgroup G} {z : G}
    (hY : Y < ⊤) (hzY : z ∈ Y) : Nat.card (properHull Y z) < Nat.card G :=
  (Subgroup.card_le_of_le (properHull_le Y hzY)).trans_lt (proper_subgroup_card_lt hY)

theorem properHull_strong_embedding [Finite G] {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hY : Y < ⊤)
    (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    fusionStronglyEmbedded (H.subgroupOf (properHull Y z)) := by
  obtain ⟨hlocal, hcentral⟩ := proper_subgroup_local_datum h hzY hescape
  have hstrong := h.smaller Y (proper_subgroup_card_lt hY)
    (H.subgroupOf Y) (⟨z, hzY⟩ : Y) hlocal hcentral
  have hmap := hstrong.map_mulEquiv (properHullEquiv Y hzY)
  rwa [properHullEquiv_point_map] at hmap

theorem properHull_class_eq [Finite G] {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    conjugacyWithin Y z = conjugacyWithin (properHull Y z) z := by
  have hlocal := local_datum_subgroup_inheritance h Y hzY hescape
  let zY : Y := ⟨z, hzY⟩
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have ht : rightConjugateElem zY y ∈ involutionPointClass zY := ⟨y, rfl⟩
    rw [localPointHull_pointClass_eq_internal_class hlocal] at ht
    obtain ⟨t, ⟨l, rfl⟩, hl⟩ := ht
    refine ⟨properHullEquiv Y hzY l, ?_⟩
    have heq := congrArg (fun a : Y => (a : G)) hl
    exact heq.trans hy
  · rintro ⟨l, hl⟩
    exact ⟨⟨l, properHull_le Y hzY l.property⟩, hl⟩

theorem properHull_point_factorization [Finite G] {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    ((H ⊓ Y : Subgroup G) : Set G) =
      ((Y ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) *
        (H ⊓ properHull Y z : Subgroup G) := by
  have hlocal := local_datum_subgroup_inheritance h Y hzY hescape
  ext x
  constructor
  · rintro ⟨hxH, hxY⟩
    have hx : (⟨x, hxY⟩ : Y) ∈ (H.subgroupOf Y : Set Y) := hxH
    rw [localPointHull_point_eq_centralizer_mul hlocal] at hx
    obtain ⟨c, hc, l, hl, heq⟩ := Set.mem_mul.mp hx
    refine Set.mem_mul.mpr ⟨c, ⟨c.property, ?_⟩, l, ⟨hl.1, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
    · rw [← internal_hull_map Y hzY]
      exact Subgroup.mem_map_of_mem Y.subtype hl.2
    · exact congrArg Subtype.val heq
  · rintro ⟨c, hc, l, hl, rfl⟩
    exact ⟨H.mul_mem (point_centralizer_le h hc.2) hl.1,
      Y.mul_mem hc.1 (properHull_le Y hzY hl.2)⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
