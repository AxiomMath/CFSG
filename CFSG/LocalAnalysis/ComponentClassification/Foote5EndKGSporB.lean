module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Sporadic.SmallOddCore.HeLocal
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGEven

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.Sporadic.Schreier (centralizerIn)

variable {X : Type} [Group X] [Finite X] {z : X} {K : Subgroup X}

theorem isComponentOf_of_oddCore (hK : IsTwoComponentAt z K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥) :
    Assembly.IsComponentOf K (centralizer ({z} : Set X)) :=
  (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.2.1).2
    (isComponent_of_oddCore hK hcore).1

theorem false_of_card_quotient_center_eq_20160 (hK : IsTwoComponentAt z K)
    (hKs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hKt : FooteFamilyType K)
    (hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥)
    (h : Nat.card (K ⧸ center K) = 20160) : False := by
  obtain ⟨hs, hna, hZ⟩ := simple_of_oddCore hK hKs hKt hcore
  have hZK : center K = Open.fusionZStar K := (center_eq_bot_of_isSimpleGroup hna).trans hZ.symm
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZK).toEquiv] at h
  rcases card_of_footeFamilyType hKt with h2 | ⟨q, hq, h5, h2⟩
  · exact not_footeOrder_20160 (Or.inl (h ▸ h2))
  · exact not_footeOrder_20160 (Or.inr ⟨q, hq, h5, h ▸ h2⟩)

theorem hs_card_inf_centralizer_component
    {T : Type} [Group T] (e : T ≃* NativeSporadic.HS) {t : T} (ht : orderOf t = 2)
    {B : Subgroup T} (hB : Assembly.IsComponentOf B (centralizer ({t} : Set T))) :
    Nat.card ↥(centralizer ({t} : Set T) ⊓ centralizer (B : Set T)) = 2 :=
  Sporadic.SmallOddCore.card_local_of_model (e.trans Sporadic.Schreier.hsPermEquiv)
    (fun _ hτP hτ _ hB' => Sporadic.SmallOddCore.card_local_of_reps
      {Sporadic.SmallOddCore.hsT1, Sporadic.SmallOddCore.hsT2}
      Sporadic.SmallOddCore.hs_reps.2.2.2.2
      (fun r hr B' hB'' => by
        rcases hr with rfl | rfl
        · exact (Sporadic.SmallOddCore.hsC1_no_component hB'').elim
        · rw [Sporadic.SmallOddCore.hsC2_component hB'']
          exact Sporadic.SmallOddCore.hs_D_facts.2.2.2.2)
      hτP hτ hB')
    ht hB

theorem endKnownGroupsInputOn_HS
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .HS) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  have hcore := oddCore_centralizer_eq_bot_of_sporadicOddCoreFree
    CatalogueU.sporadicOddCoreFree_HS (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1
  have h2 := hs_card_inf_centralizer_component e hK.1 (isComponentOf_of_oddCore hK hcore)
  exact false_of_le_of_not_eight_dvd hK hcore hD hDd hD8 le_rfl (by rw [h2]; decide)

theorem endKnownGroupsInputOn_He
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .He) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  let ψ : X ≃* Sporadic.HeldB.heP := e.trans Sporadic.HeldB.heEquivP
  have hcore : CFSG.oddCore (centralizer ({z} : Set X)) = ⊥ :=
    Sporadic.HeldB.oddCore_eq_bot_of_mulEquiv
      ((RestrictedStd.Spor.centralizerEquiv ψ z).trans
        (RestrictedStd.Spor.centralizerSubtypeEquiv _ (ψ z)))
      (Sporadic.HeldB.heP_centralizerIn_oddCore (ψ z).2
        (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hK.1]))
  exact false_of_card_quotient_center_eq_20160 hK hKs hKt hcore
    (Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order ⟨e⟩ hK.1
      (isComponentOf_of_oddCore hK hcore))

theorem endKnownGroupsInputOn_McL
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .McL) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_McL
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    ((RestrictedStd.Spor.mcl_inner_comps e z hK.1).mono fun Y _ h =>
      RestrictedStd.Spor.not_small_of_mclX h)

theorem endKnownGroupsInputOn_Suz
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Suz) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_component_card hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Suz
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB =>
      Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e z hK.1 B hB

theorem endKnownGroupsInputOn_ONan
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .ONan) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_component_card hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree Sporadic.ONOddCore.sporadicOddCoreFree_ONan
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB =>
      Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
        ⟨e⟩ z hK.1 B hB

theorem endKnownGroupsInputOn_Ru
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Ru
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    ((RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
      RestrictedStd.Spor.isoInvariant_not_three_dvd RestrictedStd.Spor.ru_centralizerIn_comps
      (e.trans Sporadic.RuSchreier.ruEquivP) z hK.1).mono fun Y _ h =>
        RestrictedStd.Spor.not_small_of_not_three h)

theorem endKnownGroupsInputOn_Co1
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Co1) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Co1
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => RestrictedStd.Spor.not_small_of_card_quotient (by
      rw [(RestrictedStd.Spor.co1LocalComponentsInput_holds X e z hK.1 B hB).1]
      exact RestrictedStd.Spor.not_isSmallOrder_G24)

theorem endKnownGroupsInputOn_Co2
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Co2) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    fun B hB => absurd hB
      (Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e z hK.1 B)

theorem endKnownGroupsInputOn_Co3
    : EndKnownGroupsInputOn fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .Co3) := by
  refine endKnownGroupsInputOn_of_false fun X _ _ _ ⟨e⟩ z K D hK hKs hKt hD hDd hD8 => ?_
  exact false_of_compsSatisfy_not_small hK hKs hKt
    (oddCore_centralizer_eq_bot_of_sporadicOddCoreFree Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
      (exists_mul_ne_mul_of_isTwoComponentAt hK) e hK.1)
    ((RestrictedStd.Spor.co3_inner_comps e z hK.1).mono fun Y _ h =>
      RestrictedStd.Spor.not_small_of_mem_co3Orders h)

end CFSG.ComponentClassification.Foote5
