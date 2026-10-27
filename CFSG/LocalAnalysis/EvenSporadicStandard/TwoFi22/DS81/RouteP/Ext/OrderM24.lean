module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Arr
public import CFSG.Sporadic.Presentation.M24Exact
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen TauCeti Certificates.RouteP.M24Defect

private theorem m24_presentation_eq :
    SporadicName.M24.presentation = Sporadic.m24Presentation := rfl

theorem m24Presentation_generatorCount : Sporadic.m24Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem relWords_eq : relWords = Sporadic.m24Presentation.relatorLetters := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.m24Presentation_transcribed]
  simp [FreeGroup.invRev, relWords]

theorem exists_subgroup_card_le {G : Type*} [Group G] (x y : G)
    (h : ∀ r ∈ relWords, wordProd (img2 x y) r = 1) :
    ∃ H : Subgroup G, x ∈ H ∧ y ∈ H ∧ Finite H ∧ Nat.card H ≤ 244823040 := by
  rw [relWords_eq] at h
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Presentation.M24.finite_card_le
  rw [SporadicName.Group, m24_presentation_eq] at hfin hcard
  let f := presHom Sporadic.m24Presentation (img2 x y) h
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  haveI := hfin
  refine ⟨f.range, ⟨presGen Sporadic.m24Presentation 0, ?_⟩,
    ⟨presGen Sporadic.m24Presentation 1, ?_⟩, Finite.of_surjective _ hsurj,
    (Nat.card_le_card_of_surjective _ hsurj).trans hcard⟩
  · rw [presHom_presGen _ _ _ (by rw [m24Presentation_generatorCount]; omega)]
    simp [img2]
  · rw [presHom_presGen _ _ _ (by rw [m24Presentation_generatorCount]; omega)]
    simp [img2]

theorem exists_subgroup_card_le_autPerm
    {G : Type*} [Group G] (x y : G)
    (h : ∀ r ∈ relWords, wordProd (img2 x y) r = 1) :
    ∃ H : Subgroup G, x ∈ H ∧ y ∈ H ∧ Finite H ∧ Nat.card H ≤ Nat.card ↥AutPerm := by
  obtain ⟨H, hx, hy, hf, hc⟩ := exists_subgroup_card_le x y h
  exact ⟨H, hx, hy, hf, hc.trans_eq card_AutPerm.symm⟩

theorem closure_genA_genB :
    Subgroup.closure ({genA, genB} : Set ↥AutPerm) = ⊤ := by
  have h : AutPerm = Subgroup.closure {bridgePA, bridgePB⁻¹} := by
    rw [AutPerm_eq_closure]
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro g (rfl | rfl)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have hb : bridgePB⁻¹ ∈
            Subgroup.closure ({bridgePA, bridgePB⁻¹} : Set (Equiv.Perm (Fin 24))) :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        simpa using Subgroup.inv_mem _ hb
    · rintro g (rfl | rfl)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have hb : bridgePB ∈
            Subgroup.closure ({bridgePA, bridgePB} : Set (Equiv.Perm (Fin 24))) :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        exact Subgroup.inv_mem _ hb
  exact CFSG.Sporadic.Mathieu.closure_pair_eq_top h bridgePA_mem (AutPerm.inv_mem bridgePB_mem)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
