module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorClass
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_centralizer_class_image
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let Y := Subgroup.centralizer ({u} : Set G)
    let zY : Y := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
    Y.subtype '' involutionPointClass zY = involutionPointClass z ∩ (Y : Set G) := by
  let Y := Subgroup.centralizer ({u} : Set G)
  let zY : Y := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
  let L := localInvolutionPointHull z u
  let zL : L := ⟨z, distinguished_mem_localInvolutionPointHull huz⟩
  obtain ⟨_, hmap, _⟩ := original_local_hull_internal_class h u huz
    (h.local_embedding u hu huz hescape)
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    exact ⟨⟨(c : G), congrArg Subtype.val hc⟩, y.property⟩
  · intro hx
    have hximage : x ∈ (Subtype.val '' involutionPointClass zL : Set G) := by
      rw [hmap]
      exact hx
    obtain ⟨s, ⟨l, hl⟩, hs⟩ := hximage
    let cY : Y := ⟨(l : G), localInvolutionPointHull_le_centralizer z u l.property⟩
    refine ⟨⟨x, hx.2⟩, ⟨cY, ?_⟩, rfl⟩
    apply Subtype.ext
    exact (congrArg Subtype.val hl).trans hs

theorem original_internal_centralizer_hull_map
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let Y := Subgroup.centralizer ({u} : Set G)
    let zY : Y := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
    (involutionPointHull zY).map Y.subtype = localInvolutionPointHull z u := by
  dsimp only
  rw [involutionPointHull, MonoidHom.map_closure,
    original_centralizer_class_image h u hu huz hescape]
  rfl

theorem original_centralizer_base_orbit_eq_local_hull
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    numeratorRightOrbit H (Subgroup.centralizer ({u} : Set G)) (rightCosetMk H 1) =
      numeratorRightOrbit H (localInvolutionPointHull z u) (rightCosetMk H 1) := by
  let Y := Subgroup.centralizer ({u} : Set G)
  let zY : Y := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.symm⟩
  have hlocal : InvolutionPointLocalEmbedding (H.subgroupOf Y) zY :=
    local_datum_subgroup_inheritance h Y zY.property hescape
  have hmap := original_internal_centralizer_hull_map h u hu huz hescape
  ext omega
  constructor
  · intro homega
    obtain ⟨l, hl⟩ := localNormalizer_internal_hull_transitive_original_orbit H Y zY hlocal
      ⟨rightCosetMk H 1, numeratorRightOrbit_base H Y (rightCosetMk H 1)⟩
      ⟨omega, homega⟩
    refine ⟨((l : Y) : G), ?_, hl⟩
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨(l : Y), l.property, rfl⟩
  · rintro ⟨l, hl, hlo⟩
    exact ⟨l, localInvolutionPointHull_le_centralizer z u hl, hlo⟩

theorem original_central_sylow_local_hull_full_fixed_set
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    elementFixedSet H u =
      numeratorRightOrbit H (localInvolutionPointHull z u) (rightCosetMk H 1) := by
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    apply point_centralizer_le h
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter) ⟨s, hs⟩)
  have hfixed := (unique_central_sylow_involution_centralizers_transitive_fixed_set
    S H hSH z hzS hzcenter h.distinguished_order h.unique_containment u huH hu).1
  have horbit : elementFixedSet H u =
      numeratorRightOrbit H (Subgroup.centralizer ({u} : Set G)) (rightCosetMk H 1) := by
    simpa only [elementFixedSet, numeratorRightOrbit, pointRightCosetMul_eq_translate]
      using hfixed
  exact horbit.trans (original_centralizer_base_orbit_eq_local_hull h u hu huz hescape)

theorem original_pair_full_fixed_set
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (huH : u ∈ H) (hu : orderOf u = 2)
    (huz : Commute u z) (hut : Commute u t)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b) :
    elementFixedSet H u =
      numeratorRightOrbit H (localInvolutionPointHull z u) (rightCosetMk H 1) :=
  original_central_sylow_local_hull_full_fixed_set h S hzS hzcenter u huH hu huz
    (original_pair_centralizer_escapes H b hb u t hut hflip)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
