module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyAlign
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllProved

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.OmegaPilot (OmegaCatalogueClausesAt)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

local instance e7PilotQ2FamilyMainNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Transport

variable {K K' : Type} [Field K] [Field K']

theorem map_posJE7_le_of_ringEquiv (ε : K ≃+* K') :
    (posJE7 K).map (adjointGroupE7OfRingEquiv ε).toMonoidHom ≤ posJE7 K' := by
  rintro _ ⟨g, hg, rfl⟩
  exact baseChangeGL_mem_highRootSL2_of_E7 (ε : K →+* K') hg

theorem map_perpLevi_of_ringEquiv (ε : K ≃+* K') :
    (EPilot.perpLevi .E7 K).map (adjointGroupE7OfRingEquiv ε).toMonoidHom =
      EPilot.perpLevi .E7 K' := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact mem_subgroupOf.2 (baseChangeGL_mem_rootSpan_perpRoots_E7 (ε : K →+* K') ⟨g, hg⟩)
  · refine ⟨(adjointGroupE7OfRingEquiv ε).symm y,
      mem_subgroupOf.2 (baseChangeGL_mem_rootSpan_perpRoots_E7 (ε.symm : K' →+* K) ⟨y, hy⟩), ?_⟩
    exact MulEquiv.apply_symm_apply _ y

variable {G : Type} [Group G] {L : Subgroup G}

theorem exists_neighbourOvergroupOmegaField_congr {X X' D D' : Subgroup G} {t : G}
    (hX : X = X') (hD : D = D') {m f : ℕ}
    (h : ∃ htX : t ∈ centralizer (X : Set G), NeighbourOvergroupOmegaField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f) :
    ∃ htX : t ∈ centralizer (X' : Set G), NeighbourOvergroupOmegaField
      (QuotientGroup.mk' (oddCore (centralizer (X' : Set G))) ⟨t, htX⟩)
      ((D'.subgroupOf (centralizer (X' : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X' : Set G))))) m f := by
  subst hX hD
  exact h

theorem hr8FieldE7Two_trans_ringEquiv {e : L ≃* adjointGroup .E7 K} {t : G} {f : ℕ}
    (ε : K ≃+* K') (h : HR8FieldE7Two e t f) :
    HR8FieldE7Two (e.trans (adjointGroupE7OfRingEquiv ε)) t f := by
  obtain ⟨A, hAJ, hA, htX, hF⟩ := h
  set φ := adjointGroupE7OfRingEquiv ε with hφ
  have hcomp : (e.trans φ).symm.toMonoidHom.comp φ.toMonoidHom = e.symm.toMonoidHom := by
    ext x
    simp
  have hA' : (A.map φ.toMonoidHom).map (e.trans φ).symm.toMonoidHom = A.map e.symm.toMonoidHom := by
    rw [Subgroup.map_map, hcomp]
  have hD' : (EPilot.perpLevi .E7 K').map (e.trans φ).symm.toMonoidHom =
      (EPilot.perpLevi .E7 K).map e.symm.toMonoidHom := by
    rw [← map_perpLevi_of_ringEquiv ε, Subgroup.map_map, hcomp]
  have hX : ((A.map φ.toMonoidHom).map (e.trans φ).symm.toMonoidHom).map L.subtype =
      (A.map e.symm.toMonoidHom).map L.subtype := by
    rw [hA']
  have hD : ((EPilot.perpLevi .E7 K').map (e.trans φ).symm.toMonoidHom).map L.subtype =
      ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hD']
  refine ⟨A.map φ.toMonoidHom, (Subgroup.map_mono hAJ).trans (map_posJE7_le_of_ringEquiv ε),
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective, hA, Nat.card_congr ε.toEquiv]
  · exact exists_neighbourOvergroupOmegaField_congr hX.symm hD.symm ⟨htX, hF⟩

end Transport

section Main

theorem e7TwoFieldRowFamilyInput_holds : E7TwoFieldRowFamilyInput := by
  intro G _ _ L K _ e t hw hF
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, -, hk⟩ := F4Pilot.exists_quadraticFrobenius_F4 (f := 1) le_rfl
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hw.card_eq]
  set ε : K ≃+* fixSubfield σ := FiniteField.ringEquivOfCardEq hc with hε
  set e' : L ≃* adjointGroup .E7 (fixSubfield σ) := e.trans (adjointGroupE7OfRingEquiv ε)
    with he'
  have hw' : E7Work L (fixSubfield σ) t 1 :=
    ⟨hw.seitz, hw.one_le, hk, hw.orderOf_eq, hw.mem_centralizer⟩
  have hF' : HR8FieldE7Two e' t 1 := hr8FieldE7Two_trans_ringEquiv ε hF
  have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hk, pow_one]
  have hK4 : Nat.card K₂ = 2 ^ 2 := by rw [hK₂]
  obtain ⟨A, hAJ, hA, Φ₀, hΦ₀⟩ :=
    E7Work.exists_fieldIdentification_nonsplit_two hσ (by rw [hK₂]; norm_num) e' hw' hF'
  let P₀ : TwoFieldParam σ e' .high
      (centralizerPerfectCore ((A.map e'.symm.toMonoidHom).map L.subtype)) := ⟨Φ₀, hΦ₀⟩
  have hE : ∀ N : E7Neighbour,
      (centralizerPerfectCore ((A.map e'.symm.toMonoidHom).map L.subtype)).map
        (MulAut.conj ((e'.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom =
          centralizerPerfectCore (nonsplitNeighbourE7G e' A N) := by
    intro N
    rw [F4Pilot.map_centralizerPerfectCore,
      ← E8Pilot.map_map_symm_map_conj e' A (N.rep (fixSubfield σ))]
    rfl
  let PN : ∀ N : E7Neighbour,
      TwoFieldParam σ e' N (centralizerPerfectCore (nonsplitNeighbourE7G e' A N)) :=
    fun N => (P₀.toNeighbour N).congr (hE N)
  obtain ⟨ρhs, hρhs, h2p, h2n⟩ := (PN .high).exists_twistAt_single_of_map_eq (PN .seven)
    (j := 2) (by decide) (by decide)
    (map_leviPiece_node_eq_of_frame hk2 hK4 e' hAJ hA .hs (PN .high) (PN .seven))
  obtain ⟨ρhf, hρhf, h5p, h5n⟩ := (PN .high).exists_twistAt_single_of_map_eq (PN .four)
    (j := 5) (by decide) (by decide)
    (map_leviPiece_node_eq_of_frame hk2 hK4 e' hAJ hA .hf (PN .high) (PN .four))
  obtain ⟨ρsf, -, h0p, h0n⟩ := (PN .seven).exists_twistAt_single_of_map_eq (PN .four)
    (j := 0) (by decide) (by decide)
    (map_leviPiece_node_eq_of_frame hk2 hK4 e' hAJ hA .sf (PN .seven) (PN .four))
  obtain ⟨a1, a2, a3⟩ := exists_aligned_twoFieldParam (PN .high) (PN .seven) (PN .four) hρhs hρhf
    (TwoFieldParam.twistOn_high_seven ⟨h2p, h2n⟩) (TwoFieldParam.twistOn_high_four ⟨h5p, h5n⟩)
    (TwoFieldParam.twistOn_seven_four ⟨h0p, h0n⟩)
  have hal := twoFieldAligned_ofTriple
    (EN := fun N => centralizerPerfectCore (nonsplitNeighbourE7G e' A N)) a1 a2 a3
  exact ⟨K₂, inferInstance, inferInstance, inferInstance, σ, e', _, hK₂,
    isTwoFieldFamily_twoAlignedFamily hal,
    centralizer_le_normalizer_range_twoAlignedFamily hk2 hK4 hAJ hA _⟩

theorem e7TwoFieldRowCTInput_holds : E7TwoFieldRowCTInput :=
  e7TwoFieldRowCTInput_of_family e7TwoFieldRowFamilyInput_holds

theorem e7TwoFieldRowInput_holds : E7TwoFieldRowInput :=
  e7TwoFieldRowInput_of_CT e7TwoFieldRowCTInput_holds

end Main

section GLS3

theorem seitzExclusion_highE7_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_q2_fieldRow hGLS (CrossChar.omegaNotOddLieInputAt 6)
    (OmegaPilot.catOmegaSporadicAt 6) e7TwoFieldRowInput_holds

end GLS3

end CFSG.SeitzReduction.E7Pilot
