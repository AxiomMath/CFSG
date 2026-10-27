module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_whole_root_and_translate_class_inclusions
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (U : Subgroup G) (hU : (U : Set G) = cosetUnitSet H z u) :
    {w : G | w ∈ U ∧ w ≠ 1} ⊆ involutionPointClass z ∧
      (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1} ⊆
        involutionPointClass (u * z) := by
  have hzU : z ∈ U := by
    change z ∈ (U : Set G)
    rw [hU]
    exact Or.inr ⟨⟨distinguished_mem_pointClass z,
      Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq⟩, h.distinguished_mem⟩
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp h.distinguished_order).2
  have htranslate : (fun v : G => u * v) '' (U : Set G) =
      translatedCosetUnitSet H z u := by rw [hU]; rfl
  refine ⟨?_, ?_⟩
  · intro w hw
    have hwset : w ∈ cosetUnitSet H z u := hU ▸ hw.1
    exact (hwset.resolve_left (fun heq => hw.2 (Set.mem_singleton_iff.mp heq))).1.1
  · rintro x ⟨w, hw, rfl⟩
    have huzmem : u * z ∈ translatedCosetUnitSet H z u :=
      htranslate ▸ (show u * z ∈ (fun v : G => u * v) '' (U : Set G) from ⟨z, hzU, rfl⟩)
    have huwmem : u * w ∈ translatedCosetUnitSet H z u :=
      htranslate ▸ (show u * w ∈ (fun v : G => u * v) '' (U : Set G) from ⟨w, hw.1, rfl⟩)
    have huzne : u * z ≠ u := by
      intro heq
      exact hz1 (mul_left_cancel (heq.trans (mul_one u).symm))
    have huwne : u * w ≠ u := by
      intro heq
      exact hw.2 (mul_left_cancel (heq.trans (mul_one u).symm))
    obtain ⟨a, ha⟩ := original_coset_stabilizer_full_off_u_orbit
      h hu huz hescape (u * z) huzmem huzne (u * w) huwmem huwne
    exact ⟨(a : G), ha⟩

theorem original_supplied_sylow_entire_class_intersection
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (U : Subgroup G) (hU : (U : Set G) = cosetUnitSet H z u)
    (hUelem : IsElementaryAbelian 2 U)
    (T1 : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hUT : U ≤ (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
      (Subgroup.centralizer ({u} : Set G)).subtype)
    (hpartition : {x : G | x ∈
        (T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
          (Subgroup.centralizer ({u} : Set G)).subtype ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ U ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1}) :
    u * z ∈ involutionPointClass u ∧
      involutionPointClass u ∩
        (((T1 : Subgroup (Subgroup.centralizer ({u} : Set G))).map
          (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G) =
        translatedCosetUnitSet H z u := by
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2
  have hzU : z ∈ U := by
    change z ∈ (U : Set G)
    rw [hU]
    exact Or.inr ⟨⟨distinguished_mem_pointClass z,
      Subgroup.mem_centralizer_singleton_iff.mpr huz.symm.eq⟩,
      h.local_datum.distinguished_mem⟩
  have hUnontrivial : U ≠ ⊥ := by
    intro heq
    rw [heq] at hzU
    exact hz1 (Subgroup.mem_bot.mp hzU)
  have hclasses : u ∉ involutionPointClass z := by
    intro huclass
    exact original_pair_class_disjoint_distinguished_class
      h.local_datum beta hb huD u huclass (distinguished_mem_pointClass u)
  have huU : u ∉ U := by
    intro huU
    have huset : u ∈ cosetUnitSet H z u := hU ▸ huU
    rcases huset with huone | huclass
    · exact (orderOf_eq_prime_iff.mp hu).2 (Set.mem_singleton_iff.mp huone)
    · exact hclasses huclass.1.1
  obtain ⟨hUclass, hproductclass⟩ := original_whole_root_and_translate_class_inclusions
    h.local_datum hu huz hescape U hU
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  let := hsimple
  obtain ⟨hfused, hinter⟩ := three_local_involution_orbits_fusion
    hnonab u hu T1 U hUelem hUnontrivial hUT z hzU hz1 huU
      hpartition hUclass hproductclass hclasses
  have htranslate : (fun v : G => u * v) '' (U : Set G) =
      translatedCosetUnitSet H z u := by rw [hU]; rfl
  exact ⟨hfused, hinter.trans htranslate⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
