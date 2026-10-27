module

public import CFSG.LocalAnalysis.ComponentClassification.ProperSectionBReduction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieFrontier

public section

namespace CFSG.ComponentClassification.ProperSectionB

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor isComponentOf_iff_isComponent_subgroupOf)

@[expose] def OddCoreCommutators (Y : Type) [Group Y] (T : Subgroup Y) : Prop :=
  let V := normalizer (T : Set Y)
  let OV := (CFSG.Assembly.oddCore V).map V.subtype
  let π := QuotientGroup.mk' (CFSG.Assembly.oddCore Y)
  let NT := normalizer (T.map π : Set (Y ⧸ CFSG.Assembly.oddCore Y))
  ⁅(CFSG.pLayer V 2).map V.subtype, OV⁆ ≤ CFSG.Assembly.oddCore Y ∧ V.map π = NT ∧
    ∀ K : Subgroup V, CFSG.IsPComponent 2 K →
      CFSG.Assembly.IsComponentOf ((K.map V.subtype).map π) NT ∧
        ⁅(K.map V.subtype).map π, OV.map π⁆ = ⊥ ∧ ⁅K.map V.subtype, OV⁆ ≤ CFSG.Assembly.oddCore Y

@[expose] def KGroupBConclusion (Y : Type) [Group Y] : Prop :=
  CentralTwoBInclusion.Property Y ∧
    (CFSG.Assembly.oddCore Y = ⊥ →
      TwoComponents.badSubgroup Y = ⊥ ∧ CFSG.Assembly.ComponentType.LocalBProperty Y) ∧
    ∀ T : Subgroup Y, T ≠ ⊥ → IsPGroup 2 T → OddCoreCommutators Y T

theorem kProper_of_isKGroupCat {Y : Type} [Group Y] (hY : SectionRank.IsKGroupCat Y) :
    CFSG.Assembly.KProper Blueprint.Catalog Y :=
  CFSG.KCore.KGroupNonab.kProperNonab (CFSG.KCore.KGroupAllSimple.kGroupNonab hY)

theorem kGroup_B_inclusion_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput) :
    ∀ (Y : Type) [Group Y] [Finite Y], SectionRank.IsKGroupCat Y →
      CentralTwoBInclusion.Property Y := by
  have hC : ∀ {X Z : Type} [Group X] [Group Z], X ≃* Z → Blueprint.Catalog Z →
      Blueprint.Catalog X := fun e h => SectionRank.catalog_of_mulEquiv e h
  suffices h : ∀ n : ℕ, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
      SectionRank.IsKGroupCat Y → CentralTwoBInclusion.Property Y from
    fun Y _ _ hY => h _ Y rfl hY
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ hn hY
    have hsub : ∀ X : Subgroup Y, X ≠ ⊤ → CentralTwoBInclusion.Property X := by
      intro X hX
      have hlt : Nat.card X < Nat.card Y := by
        simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hX)
      exact ih _ (hn ▸ hlt) X rfl (hY.subgroup X)
    have hquot : ∀ (N : Subgroup Y) (_ : N.Normal), N ≠ ⊥ →
        CentralTwoBInclusion.Property (Y ⧸ N) := by
      intro N _ hN
      exact ih _ (hn ▸ MinimalBCenter.quotient_card_lt N hN) (Y ⧸ N) rfl (hY.quotient N)
    by_contra hfail
    obtain ⟨S, hS1, hS2, hSfail⟩ : ∃ S : Subgroup Y, S ≠ ⊥ ∧ IsPGroup 2 S ∧
        ¬ (TwoComponents.badSubgroup (normalizer (S : Set Y))).map
          (normalizer (S : Set Y)).subtype ≤ TwoComponents.badSubgroup Y := by
      by_contra hnone
      push Not at hnone
      exact hfail fun S hS1 hS2 => hnone S hS1 hS2
    obtain ⟨-, -, -, ⟨z, hz, hzS, hzc, -⟩, hlocal⟩ :=
      proper_section_B_failure_simple_unbalanced_reduction_of_schreier hC hS
        (kProper_of_isKGroupCat hY) hsub hquot hS1 hS2 hSfail
    obtain ⟨-, -, ⟨L, hL, hLq, hLB⟩, hall, hcore⟩ := hlocal z hz hzS hzc
    obtain ⟨-, -, hDF, hsimple, hnab, -, hindex⟩ := hall L hL hLq hLB _ rfl
    rw [CFSG.generalizedFitting_eq_componentClassification] at hDF
    rw [hDF] at hsimple hnab hindex
    have : IsSimpleGroup (GeneralizedFitting.subgroup Y) := hsimple
    have hcat : Blueprint.Catalog (GeneralizedFitting.subgroup Y) :=
      SectionRank.catalog_of_isKGroupCat_of_surjective hY _ (MonoidHom.id _)
        Function.surjective_id
    rcases hU Y hsimple hnab hcat ⟨z, hz, hcore⟩ with hlie | ⟨m, -, hm, ⟨θ⟩, -⟩ | ⟨hexc, -⟩
    · exact hfail
        (CatalogueBOddLie.odd_Lie_index_two_B_under_proper_subgroup_B hnab hindex hlie hsub)
    · exact hfail (CatalogueBAlternating.generalizedFitting_B_inclusion hnab (Or.inr hm) θ)
    · exact hfail
        (KProperRelativeB.exceptionalInput_of_held hheld Y hsimple hnab hindex hexc hsub)

theorem badSubgroup_eq_bot_and_localB_of_corefree {Y : Type} [Group Y] [Finite Y]
    (hB : CentralTwoBInclusion.Property Y) (hcore : CFSG.Assembly.oddCore Y = ⊥) :
    TwoComponents.badSubgroup Y = ⊥ ∧ CFSG.Assembly.ComponentType.LocalBProperty Y :=
  ⟨TwoComponents.badSubgroup_eq_bot_of_corefree hcore,
    AssemblyBLocalB.of_corefree_and_inclusion hcore hB⟩

theorem odd_quotient_component_commutators {Y : Type} [Group Y] [Finite Y] (O : Subgroup Y)
    [O.Normal] (hO2 : ¬ 2 ∣ Nat.card O)
    (hlocalB : CFSG.Assembly.ComponentType.LocalBProperty (Y ⧸ O)) (T : Subgroup Y)
    (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    ⁅(CFSG.pLayer (normalizer (T : Set Y)) 2).map (normalizer (T : Set Y)).subtype,
        (CFSG.Assembly.oddCore (normalizer (T : Set Y))).map (normalizer (T : Set Y)).subtype⁆ ≤
        O ∧
      (normalizer (T : Set Y)).map (QuotientGroup.mk' O) =
        normalizer (T.map (QuotientGroup.mk' O) : Set (Y ⧸ O)) ∧
      ∀ K : Subgroup (normalizer (T : Set Y)), CFSG.IsPComponent 2 K →
        CFSG.Assembly.IsComponentOf
            ((K.map (normalizer (T : Set Y)).subtype).map (QuotientGroup.mk' O))
            (normalizer (T.map (QuotientGroup.mk' O) : Set (Y ⧸ O))) ∧
          ⁅(K.map (normalizer (T : Set Y)).subtype).map (QuotientGroup.mk' O),
            ((CFSG.Assembly.oddCore (normalizer (T : Set Y))).map
              (normalizer (T : Set Y)).subtype).map (QuotientGroup.mk' O)⁆ = ⊥ ∧
          ⁅K.map (normalizer (T : Set Y)).subtype,
            (CFSG.Assembly.oddCore (normalizer (T : Set Y))).map
              (normalizer (T : Set Y)).subtype⁆ ≤ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := normalizer (T : Set Y) with hV
  set NT := normalizer (T.map (QuotientGroup.mk' O) : Set (Y ⧸ O)) with hNT
  have hVmap : V.map (QuotientGroup.mk' O) = NT :=
    CFSG.GroupTheory.normal_coprime_quotient_normalizer 2 O hO2 T hT2
  have hTπ : T.map (QuotientGroup.mk' O) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hdvd : Nat.card T ∣ Nat.card O := Subgroup.card_dvd_of_le hbot
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hn
      exact hT1 hn
    exact hO2 ((dvd_pow_self 2 hn0).trans (hn ▸ hdvd))
  let f : V →* NT :=
    (MulEquiv.subgroupCongr hVmap).toMonoidHom.comp ((QuotientGroup.mk' O).subgroupMap V)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hVmap).surjective.comp ((QuotientGroup.mk' O).subgroupMap_surjective V)
  have hcomp : NT.subtype.comp f = (QuotientGroup.mk' O).comp V.subtype :=
    MonoidHom.ext fun _ => rfl
  have hfmap : ∀ X : Subgroup V,
      (X.map f).map NT.subtype = (X.map V.subtype).map (QuotientGroup.mk' O) := fun X => by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hfker : ¬ 2 ∣ Nat.card f.ker := by
    have hle : f.ker.map V.subtype ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      have h1 : ((f x : NT) : Y ⧸ O) = 1 := by
        rw [hx]
        rfl
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hdvd : Nat.card f.ker ∣ Nat.card O := by
      rw [← Subgroup.card_map_of_injective V.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 => hO2 (h2.trans hdvd)
  set R := (CFSG.Assembly.oddCore V).map f with hR
  have hRnormal : R.Normal := (CFSG.Assembly.oddCore_normal V).map f hf
  have hRodd : Odd (Nat.card R) :=
    (OddCore.odd_card V).of_dvd_nat (Subgroup.card_map_dvd (CFSG.Assembly.oddCore V) f)
  have hRsolv : Group.IsSolvable R := CFSG.Milestones.odd_order_solvable hRodd
  have hRcent := (CFSG.LocalCores.component_solvable_centralizer hRsolv
    hRnormal.isSubnormal).1
  have hK : ∀ K : Subgroup V, CFSG.IsPComponent 2 K →
      CFSG.Assembly.IsComponentOf ((K.map V.subtype).map (QuotientGroup.mk' O)) NT ∧
        ⁅(K.map V.subtype).map (QuotientGroup.mk' O),
          ((CFSG.Assembly.oddCore V).map V.subtype).map (QuotientGroup.mk' O)⁆ = ⊥ ∧
        ⁅K.map V.subtype, (CFSG.Assembly.oddCore V).map V.subtype⁆ ≤ O := by
    intro K hKc
    have hKf : CFSG.IsPComponent 2 (K.map f) :=
      (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hf hfker).1.mapsTo
        hKc
    have hKtwo : CFSG.Assembly.ComponentType.IsTwoPComponent (K.map f) :=
      (AssemblyBTwoComponents.isTwoPComponent_iff_twoComponent _).2
        ((CatalogueBAlternating.pComponent_two_iff _).1 hKf)
    have hKcomp : CFSG.IsComponent (K.map f) :=
      (AssemblyBPredicates.isComponentOf_top_iff_native _).1
        (hlocalB _ hTπ (hT2.map _) (K.map f) hKtwo)
    have hKle : (K.map V.subtype).map (QuotientGroup.mk' O) ≤ NT := by
      rw [← hfmap]
      exact Subgroup.map_subtype_le _
    have hKsub : ((K.map V.subtype).map (QuotientGroup.mk' O)).subgroupOf NT = K.map f := by
      rw [← hfmap]
      exact Subgroup.comap_map_eq_self_of_injective NT.subtype_injective _
    have hKR : ⁅(K.map V.subtype).map (QuotientGroup.mk' O),
        ((CFSG.Assembly.oddCore V).map V.subtype).map (QuotientGroup.mk' O)⁆ = ⊥ := by
      rw [← hfmap, ← hfmap, ← Subgroup.map_commutator, hRcent _ hKcomp, Subgroup.map_bot]
    refine ⟨(isComponentOf_iff_isComponent_subgroupOf hKle).2 (hKsub ▸ hKcomp), hKR, ?_⟩
    rw [← QuotientGroup.ker_mk' O, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator]
    exact hKR
  refine ⟨?_, hVmap, hK⟩
  rw [← QuotientGroup.ker_mk' O, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator,
    Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.map_map,
    Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hKc => ?_
  rw [← Subgroup.map_le_iff_le_comap, ← Subgroup.map_map,
    ← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (hK K hKc).2.1

theorem kGroupBConclusion_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionRank.IsKGroupCat Y) : KGroupBConclusion Y := by
  have hB := kGroup_B_inclusion_of_inputs hS hU hheld
  refine ⟨hB Y hY, badSubgroup_eq_bot_and_localB_of_corefree (hB Y hY), fun T hT1 hT2 => ?_⟩
  have hO2 : ¬ 2 ∣ Nat.card (CFSG.Assembly.oddCore Y) := by
    obtain ⟨m, hm⟩ : Odd (Nat.card (CFSG.Assembly.oddCore Y)) := OddCore.odd_card Y
    omega
  have hcoreO : CFSG.Assembly.oddCore (Y ⧸ CFSG.Assembly.oddCore Y) = ⊥ :=
    OddCore.quotient_corefree Y
  have hlocalB := AssemblyBLocalB.of_corefree_and_inclusion hcoreO (hB _ (hY.quotient _))
  exact odd_quotient_component_commutators (CFSG.Assembly.oddCore Y) hO2 hlocalB T hT1 hT2

theorem kProper_section_B_conclusion_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    {H : Subgroup G} (hH : H ≠ ⊤) (N : Subgroup H) [N.Normal] {Y : Type} [Group Y]
    (f : H ⧸ N ≃* Y) : SectionRank.IsKGroupCat Y ∧ KGroupBConclusion Y := by
  have hHK : SectionRank.IsKGroupCat H :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK H hH
  have hYK : SectionRank.IsKGroupCat Y := (hHK.quotient N).of_mulEquiv f.symm
  have : Finite Y := Finite.of_equiv (H ⧸ N) f.toEquiv
  exact ⟨hYK, kGroupBConclusion_of_inputs hS hU hheld hYK⟩

theorem kGroup_B_inclusion_and_kProper_proper_section_availability_of_inputs
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) :
    (∀ (Y : Type) [Group Y] [Finite Y], SectionRank.IsKGroupCat Y → KGroupBConclusion Y) ∧
    (∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Blueprint.Catalog G →
      ∀ H : Subgroup G, H ≠ ⊤ → ∀ (N : Subgroup H) [N.Normal] (Y : Type) [Group Y],
        (H ⧸ N ≃* Y) → SectionRank.IsKGroupCat Y ∧ KGroupBConclusion Y) ∧
    ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Blueprint.Catalog G →
      ∀ B : Subgroup G, B ≠ ⊥ → IsPGroup 2 B → normalizer (B : Set G) ≠ ⊤ →
      ∀ H : Subgroup G, H ≤ normalizer (B : Set G) → ∀ (N : Subgroup H) [N.Normal]
        (Y : Type) [Group Y], (H ⧸ N ≃* Y) → KGroupBConclusion Y :=
  ⟨fun _ _ _ hY => kGroupBConclusion_of_inputs hS hU hheld hY,
    fun _ _ _ hK _ hH N _ _ _ f => kProper_section_B_conclusion_of_inputs hS hU hheld hK hH N f,
    fun _ _ _ hK _ _ _ hBG _ hHB N _ _ _ f =>
      (kProper_section_B_conclusion_of_inputs hS hU hheld hK
        (fun h => hBG (top_unique (h ▸ hHB))) N f).2⟩

end CFSG.ComponentClassification.ProperSectionB
