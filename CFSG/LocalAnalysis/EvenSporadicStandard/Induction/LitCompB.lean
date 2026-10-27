module

public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBSec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompMono
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Lemma36
public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBRemaining
public import CFSG.Sporadic.HeldB.IndexTwo
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification

theorem bthm_of_inclusionAt {G : Type} [Group G] [Finite G]
    (hB : CentralTwoBInclusion.Property G) (hO : CFSG.oddCore G = ⊥) (u : G)
    (hu : orderOf u = 2) : BTheoremAt u := by
  intro M hM
  have hMC : M ≤ centralizer ({u} : Set G) := CFSG.Quasithin.le_of_mem_cComp hM.1
  have hloc : LocalB.LocalBProperty G := CentralTwoBInclusion.localB_of_corefree hO hB
  have h2 := (CFSG.QuasithinUnique.I32.isTwoComponentIn_iff hMC).mp hM
  exact ⟨hMC, (CFSG.isComponent_iff_open _).mpr (LocalB.ordinary_at_involution hloc u hu _ h2)⟩

theorem fs79Lemma15CoreFreeEquality_of_inclusionAt {G : Type} [Group G] [Finite G]
    (hB : CentralTwoBInclusion.Property G) (S : Subgroup G) (hS : IsPGroup 2 S)
    (hO : CFSG.oddCore G = ⊥) :
    twoLayerIn (centralizer (S : Set G)) = layerIn (centralizer (S : Set G)) := by
  set C : Subgroup G := centralizer (S : Set G) with hC
  have key : ∀ N : Subgroup G, N ≤ C → CFSG.IsPComponent 2 (N.subgroupOf C) → IsCompIn N C := by
    intro N hNC hN
    by_cases hS1 : S = ⊥
    · have hCtop : C = ⊤ := by
        rw [hC, hS1]
        simp
      have hO2 : CFSG.pPrimeCore 2 G = ⊥ := by
        rw [← oddCore_eq_pPrimeCore_two']
        exact hO
      have hsubC : C.IsSubnormal := by
        rw [hCtop]
        exact Subgroup.IsSubnormal.top
      have hle := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hsubC
      have hOC : CFSG.oddCore ↥C = ⊥ := by
        rw [oddCore_eq_pPrimeCore_two']
        exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1
          (le_bot_iff.1 (hle.trans hO2.le))
      exact isCompIn_of_isTwoComponentIn hOC
        ((CFSG.QuasithinUnique.I32.isTwoComponentIn_iff hNC).mpr
          ((CatalogueBAlternating.pComponent_two_iff _).mp hN))
    · have hloc : LocalB.LocalBProperty G := CentralTwoBInclusion.localB_of_corefree hO hB
      have hCN : C ≤ normalizer (S : Set G) := centralizer_le_normalizer _
      have hCsub : (C.subgroupOf (normalizer (S : Set G))).IsSubnormal :=
        ((normal_subgroupOf_iff_le_normalizer hCN).mpr
          (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer S)).isSubnormal
      have hN' : CFSG.IsPComponent 2 (N.subgroupOf (normalizer (S : Set G))) :=
        GSThmB.A10T.isPComponent_of_le_of_subnormal hNC hCN hCsub hN
      have hcomp := hloc S hS1 hS _
        ((CatalogueBAlternating.pComponent_two_iff _).mp hN')
      have hcomp' : IsCompIn N (normalizer (S : Set G)) :=
        ⟨hNC.trans hCN, (CFSG.isComponent_iff_open _).mpr hcomp⟩
      obtain ⟨_, -, hsub, -⟩ := hN
      exact isCompIn_of_subnormal hNC hcomp'.isQuasisimple hsub
  apply le_antisymm
  ·
    show GSThmB.layerIn C ≤ _
    rw [GSThmB.A10T.layerIn_eq_iSup]
    exact iSup₂_le fun N hN => iSup_le fun hN2 => le_sSup (key N hN hN2)
  ·
    refine sSup_le fun M hM => ?_
    exact GSThmB.A10T.le_layerIn_of_isPComponent hM.1
      (CatFactsSp4.isPComponent_two_of_quasisimple' hM.1 hM.isQuasisimple hM.2.2
        (GSThmB.even_card_of_isQuasisimple' hM.isQuasisimple))

theorem fs79Lemma15At_of_inclusionAt {G : Type} [Group G] [Finite G]
    (hB : CentralTwoBInclusion.Property G) : FS79Lemma15At G :=
  fun hK S hS =>
    ⟨fun T hT => fs79Lemma15Monotonicity_proved G hK S hS T hT,
      fun hO => fs79Lemma15CoreFreeEquality_of_inclusionAt hB S hS hO⟩

section FromRelativeU

theorem centralTwoBInclusion_of_relativeUAt (P : ∀ (X : Type) [Group X], Prop)
    (hP : ∀ (X Y : Type) [Group X] [Group Y], P Y → CFSG.SignalizerFunctorTheorem.IsSectionOf X Y →
      P X)
    (hU : ∀ (X : Type) [Group X] [Finite X], P X →
      KProperRelativeB.RelativeUAt CFSG.Blueprint.Catalog X) :
    ∀ (G : Type) [Group G] [Finite G], P G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
      CentralTwoBInclusion.Property G :=
  KProperRelativeB.kProper_B_inclusion_of_inputs_P P hP
    (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h)
    (KProperRelativeB.reducedCounterexampleSec_of_schreier
      (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h)
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog)
    hU
    (KProperRelativeB.oddLieInput_of_frontier KProperRelativeB.oddExceptionalFrontier_holds)
    (KProperRelativeB.exceptionalInput_of_held
      fun G _ _ hs hnonab hindex hiso hproper =>
        (Sporadic.HeldB.Held_index_two_B_under_proper_subgroup_B hnonab hindex hiso hproper).2)

end FromRelativeU

end CFSG.EvenSporadicStandard.Induction
