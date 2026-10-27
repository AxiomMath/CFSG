module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineAltSeven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.Sporadic.HeldB.OuterCentQS

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

section Components

variable {E : Type*} [Group E] {B Q : Subgroup E}

theorem isComponent_le_of_index_two (hB : IsComponent B) (hQ : Q.index = 2) : B ≤ Q :=
  calc B = ⁅B, B⁆ := (Subgroup.isPerfect_iff.mp hB.1.1).symm
    _ ≤ ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ := Subgroup.commutator_mono le_top le_top
    _ ≤ Q := Sporadic.SuzOddCore.commutator_le_of_index_two hQ

theorem isComponent_ne_bot (hB : IsComponent B) : B ≠ ⊥ := by
  have : Nontrivial B := LocalCores.isQuasisimple_nontrivial hB.1
  exact (Subgroup.nontrivial_iff_ne_bot B).1 this

theorem isComponent_eq_of_le_isSimpleGroup (hB : IsComponent B) (hQ : IsSimpleGroup Q)
    (hBQ : B ≤ Q) : B = Q := by
  rcases (hB.2.subgroupOf (K := Q)).eq_bot_or_top_of_isSimpleGroup hQ with h | h
  · refine absurd ?_ (isComponent_ne_bot hB)
    rw [eq_bot_iff]
    intro b hb
    have hmem : (⟨b, hBQ hb⟩ : Q) ∈ B.subgroupOf Q := Subgroup.mem_subgroupOf.2 hb
    rw [h, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  · exact le_antisymm hBQ (Subgroup.subgroupOf_eq_top.mp h)

theorem isComponent_eq_of_le_isQuasisimple [Finite E] (hB : IsComponent B)
    (hQ : CFSG.IsQuasisimple Q) (hQn : Q.Normal) (hBQ : B ≤ Q) : B = Q := by
  rcases LocalCores.distinct_components_commute hB ⟨hQ, hQn.isSubnormal⟩ with h | h
  · exact h
  · refine absurd ?_ (isComponent_ne_bot hB)
    have hBB : ⁅B, B⁆ = ⊥ := le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hBQ).trans h.le)
    rwa [Subgroup.isPerfect_iff.mp hB.1.1] at hBB

theorem isComponentOf_map_subtype {K : Subgroup E} {B : Subgroup K} (hB : IsComponent B) :
    CFSG.Assembly.IsComponentOf (B.map K.subtype) K := by
  have hsub : (B.map K.subtype).subgroupOf K = B := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  rw [LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (Subgroup.map_subtype_le B), hsub]
  exact hB

theorem card_quotient_center_map_alt7 {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    {D : Subgroup X} (eD : D ≃* alternatingGroup (Fin 7)) :
    Nat.card (↥(D.map f.toMonoidHom) ⧸ center ↥(D.map f.toMonoidHom)) = 2520 :=
  SeitzReduction.SporadicRefine.card_quotient_center_alt_seven
    ((D.equivMapOfInjective f.toMonoidHom f.injective).symm.trans eD)

end Components

section HS

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.QuasithinUnique.Id2519.HSAut

theorem hs_outerC_false_of_alt7
    {B : Subgroup outerC} (hB : IsComponent B) (eB : B ≃* alternatingGroup (Fin 7)) : False := by
  have : IsSimpleGroup outerE := outerE_simple
  let φ : outerE.subgroupOf outerC ≃* outerE := subgroupOfEquivOfLe outerE_le_outerC
  have hBQ : B = outerE.subgroupOf outerC :=
    isComponent_eq_of_le_isSimpleGroup hB φ.isSimpleGroup
      (isComponent_le_of_index_two hB index_outerE)
  have h1 := SeitzReduction.SporadicRefine.card_alt_seven eB
  rw [hBQ, Nat.card_congr φ.toEquiv, card_outerE] at h1
  norm_num at h1

end HS

section He

open CFSG.Sporadic.HeldB

theorem he_inner_false_of_alt7
    {S : Type} [Group S] (e : S ≃* NativeSporadic.He) {u : S}
    (hu : orderOf u = 2) {B : Subgroup (centralizer ({u} : Set S))} (hB : IsComponent B)
    (eB : B ≃* alternatingGroup (Fin 7)) : False := by
  have h := Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
    ⟨e⟩ hu (isComponentOf_map_subtype hB)
  rw [SeitzReduction.SporadicRefine.card_quotient_center_alt_seven
    ((B.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eB)] at h
  norm_num at h

theorem he_outer_false_of_alt7
    {S : Type} [Group S] (e : S ≃* NativeSporadic.He) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (eD : D ≃* alternatingGroup (Fin 7)) : False := by
  set θ : S ≃* heP := e.trans heEquivP
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
    (MulAut.congr θ σ) (by rw [orderOf_congr, hσ]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  obtain ⟨hC, -⟩ := ctbh_outer_centralizer_small_action_arithmetic
  let f : fixedSubgroup σ ≃* heOuterC :=
    (((fixedSubgroupCongr θ σ).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
      (fixedSubgroupEquivOfConj x hg heAutU hxg)).trans (MulEquiv.subgroupCongr hC.symm)
  obtain ⟨-, hq, hi⟩ := ctbh_outer_centralizer_derived_quasisimple
  let φ : heOuterD.subgroupOf heOuterC ≃* heOuterD := subgroupOfEquivOfLe heOuterD_le_C
  have hQi : (heOuterD.subgroupOf heOuterC).index = 2 := hi
  have hB := LocalCores.isComponent_map_mulEquiv f hD
  have hBQ : D.map f.toMonoidHom = heOuterD.subgroupOf heOuterC :=
    isComponent_eq_of_le_isQuasisimple hB (hq.of_mulEquiv φ) (normal_of_index_eq_two hQi)
      (isComponent_le_of_index_two hB hQi)
  have h1 := SeitzReduction.SporadicRefine.card_alt_seven
    ((D.equivMapOfInjective f.toMonoidHom f.injective).symm.trans eD)
  rw [hBQ, Nat.card_congr φ.toEquiv, card_heOuterD] at h1
  norm_num at h1

end He


open CFSG.SeitzReduction.SporadicRefine in
theorem false_of_sporadic_alt7_weak {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {τ : MulAut S}
    (hτ : orderOf τ = 2) {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (eD : D ≃* alternatingGroup (Fin 7)) : False := by
  have := hS
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    omega
  have hDcard : Nat.card D = 2520 := card_alt_seven eD
  have hdvdC : 2520 ∣ Nat.card (fixedSubgroup τ) := hDcard ▸ card_subgroup_dvd_card D
  have hdvdS : 2520 ∣ Nat.card S := hdvdC.trans (card_subgroup_dvd_card _)
  obtain ⟨s, ⟨e⟩⟩ := hsp
  cases s
  case M12 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12] at hdvdS
    norm_num at hdvdS
  case J1 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J1.card_J1] at hdvdS
    norm_num at hdvdS
  case J3 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J3.card_J3] at hdvdS
    norm_num at hdvdS
  case J2 =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      have hu := orderOf_eq_two_of_conj_of_simple hS hna hτ
      rw [Nat.card_congr (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf u)).toEquiv]
        at hdvdC
      rcases j2_card_centralizer e hu with h | h <;> rw [h] at hdvdC <;> norm_num at hdvdC
    · rw [j2_card_fixedSubgroup_outer e hτ hin] at hdvdC
      norm_num at hdvdC
  case HS =>
    obtain ⟨r, hr, ⟨ψ⟩⟩ := hs_fixedSubgroup_rows e hτ
    obtain ⟨-, -, -, hrows, -, -, -, -⟩ := Sporadic.SmallOddCore.hs_involution_centralizers
    have hcardC := (hrows r hr).2.2.2.2.1
    rw [Nat.card_congr ψ.toEquiv, hcardC] at hdvdC
    rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h | ⟨-, -, h, -⟩ | ⟨hrep, -⟩ | h
    · rw [h] at hdvdC
      norm_num at hdvdC
    · rw [h] at hdvdC
      norm_num at hdvdC
    · let ψ' : fixedSubgroup τ ≃* QuasithinUnique.Id2519.HSAut.outerC :=
        ψ.trans (MulEquiv.subgroupCongr (by rw [hrep]; rfl))
      exact hs_outerC_false_of_alt7 (LocalCores.isComponent_map_mulEquiv ψ' hD)
        ((D.equivMapOfInjective ψ'.toMonoidHom ψ'.injective).symm.trans eD)
    · rw [h] at hdvdC
      norm_num at hdvdC
  case He =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      obtain ⟨B', hB', ⟨χ⟩⟩ := isComponent_map_fixedSubgroup_conj rfl hD
      exact he_inner_false_of_alt7 e (orderOf_eq_two_of_conj_of_simple hS hna hτ) hB'
        (χ.trans eD)
    · exact he_outer_false_of_alt7 e hτ hin hD eD
  case Suz =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      obtain ⟨B', hB', ⟨χ⟩⟩ := isComponent_map_fixedSubgroup_conj rfl hD
      have h := Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u
        (orderOf_eq_two_of_conj_of_simple hS hna hτ) B' hB'
      rw [card_quotient_center_alt_seven (χ.trans eD)] at h
      norm_num at h
    · let φ := MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub τ)
      have h := ComponentClassification.SolMax.suzOuterComponentsInput_holds S ⟨e⟩ τ hτ2 hin
        (D.map φ.toMonoidHom) (LocalCores.isComponent_map_mulEquiv φ hD)
      rw [card_quotient_center_map_alt7 φ eD] at h
      norm_num at h
  case ONan =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      obtain ⟨B', hB', ⟨χ⟩⟩ := isComponent_map_fixedSubgroup_conj rfl hD
      have h :=
        Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
          ⟨e⟩ u (orderOf_eq_two_of_conj_of_simple hS hna hτ) B' hB'
      rw [card_quotient_center_alt_seven (χ.trans eD)] at h
      norm_num at h
    · let φ := MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub τ)
      have h := ComponentClassification.SolMax.onOuterComponentsInput_of_local
        ComponentClassification.SolMax.ONOut.onOuterLocalInput_holds S ⟨e⟩ τ hτ2 hin
        (D.map φ.toMonoidHom) (LocalCores.isComponent_map_mulEquiv φ hD)
      rw [card_quotient_center_map_alt7 φ eD] at h
      norm_num at h
  case M11 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M11 hna e
      hτ2 hτ1 hD eD
  case M22 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M22 hna e
      hτ2 hτ1 hD eD
  case M23 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M23 hna e
      hτ2 hτ1 hD eD
  case M24 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M24 hna e
      hτ2 hτ1 hD eD
  case J4 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_J4 hna e
      hτ2 hτ1 hD eD
  case McL =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_McL hna e
      hτ2 hτ1 hD eD
  case Ru =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Ru hna e
      hτ2 hτ1 hD eD
  case Co1 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Co1 hna e
      hτ2 hτ1 hD eD
  case Co2 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Co2 hna e
      hτ2 hτ1 hD eD
  case Co3 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Co3 hna e
      hτ2 hτ1 hD eD
  case Fi22 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Fi22 hna e
      hτ2 hτ1 hD eD
  case Fi23 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Fi23 hna e
      hτ2 hτ1 hD eD
  case Fi24Prime =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Fi24Prime
      hna e hτ2 hτ1 hD eD
  case HN =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_HN hna e
      hτ2 hτ1 hD eD
  case Ly =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Ly hna e
      hτ2 hτ1 hD eD
  case Th =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Th hna e
      hτ2 hτ1 hD eD
  case B =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_B hna e
      hτ2 hτ1 hD eD
  case M =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M hna e
      hτ2 hτ1 hD eD

end CFSG.OddStandard.AltStdSec
