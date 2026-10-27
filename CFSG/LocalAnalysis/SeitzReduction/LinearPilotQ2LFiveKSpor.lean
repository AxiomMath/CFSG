module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoONLocal
public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34HS
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ON
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Small
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Suz
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSym

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy transportAut
  transportAut_mul_self transportAut_not_mem_inner fixSubTransportEquiv mem_inner_of_mulEquiv
  compsSatisfy_centralizer_of_mulEquiv isoInvariant_not_three_dvd isoInvariant_card_dvd
  isoInvariant_card_quotient_center compsSatisfy_of_isQuasisimple)

theorem three_dvd_card_of_card_quotient_center_lThree {G : Type*} [Group G] {D : Subgroup G}
    (hcard : Nat.card (D ⧸ center D) = 168) : 3 ∣ Nat.card D :=
  (show 3 ∣ 168 by norm_num).trans (hcard ▸ card_quotient_dvd_card _)

theorem card_centralizer_singleton_of_mulEquiv {A B : Type*} [Group A] [Group B] (ε : A ≃* B)
    (x : A) : Nat.card (centralizer ({x} : Set A)) = Nat.card (centralizer ({ε x} : Set B)) := by
  have h : (centralizer ({x} : Set A)).map ε.toMonoidHom = centralizer ({ε x} : Set B) := by
    ext y
    simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨ε.symm y, ?_, ε.apply_symm_apply y⟩
      apply ε.injective
      rw [map_mul, map_mul, ε.apply_symm_apply, hy]
  rw [← h, card_map_of_injective ε.injective]

section M22


theorem m22_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
    have h : Nat.card (D.map φ.toMonoidHom) ∣ 384 :=
      compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M22 (isoInvariant_card_dvd 384)
        ComponentClassification.RestrictedStd.Spor.m22_centralizerIn_comps e s hs _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    have h2 : 168 ∣ 384 := hcard ▸ (card_quotient_dvd_card _).trans h
    norm_num at h2
  · have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    let φ := (MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_eq_fixSub' σ)).trans
      (fixSubTransportEquiv e σ)
    have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
      ComponentClassification.RestrictedStd.Spor.m22_outer_comps (transportAut e σ)
        (transportAut_mul_self e hσ2) (transportAut_not_mem_inner e hin) _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    exact h (three_dvd_card_of_card_quotient_center_lThree hcard)

end M22

section M23


theorem m23_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m23_all_inner β
    exact ⟨h, hh.symm⟩) σ
  have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M23 isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.m23_centralizerIn_comps e s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center_lThree hcard)

end M23

section M24


theorem m24_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M24) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m24_all_inner β
    exact ⟨h, hh.symm⟩) σ
  have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M24 isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.m24_centralizerIn_comps e s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center_lThree hcard)

end M24

section Ru


theorem ru_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Ru) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  set θ := e.trans Sporadic.RuSchreier.ruEquivP
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv θ Sporadic.RuSchreier.mulAut_inner σ
  have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv Sporadic.RuSchreier.ruP isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.ru_centralizerIn_comps θ s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_card_quotient_center_lThree hcard)

end Ru

section Ly


theorem ly_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Ly) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  have hall : ∀ β : MulAut (NativeSporadic.Carrier .Ly),
      ∃ h : NativeSporadic.Carrier .Ly, β = MulAut.conj h := by
    intro β
    have hβ : β ∈ ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput]
      trivial
    obtain ⟨h, hh⟩ := hβ
    exact ⟨h, hh.symm⟩
  have hin : σ ∈ (MulAut.conj : S →* MulAut S).range := mem_inner_of_mulEquiv e hall σ
  obtain ⟨s, rfl⟩ := hin
  have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ s hs
  have hcardC : Nat.card (centralizer ({s} : Set S) ⧸ center (centralizer ({s} : Set S))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
  have h : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 19958400 :=
    compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400}) hcardC _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  obtain ⟨ψ⟩ := SporadicRefine.nonempty_quotient_center_map_equiv φ D
  rw [← Nat.card_congr ψ.toEquiv, hcard] at h
  norm_num at h

end Ly

section J1


theorem j1_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .J1) {σ : MulAut S}
    (hσ : orderOf σ = 2) (D : Subgroup (fixedSubgroup σ))
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.isInnerAut_of_carrierJ1 e σ
  have hσc : σ = MulAut.conj l⁻¹ := by
    ext x
    rw [hl x, MulAut.conj_apply, inv_inv]
  subst hσc
  have hs : orderOf l⁻¹ = 2 := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
  set ε : S ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm with hεdef
  have hε : orderOf (ε l⁻¹) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hs
  have hC : Nat.card (fixedSubgroup (MulAut.conj l⁻¹)) = 120 := by
    rw [SporadicRefine.fixedSubgroup_conj_eq_centralizerOf,
      card_centralizer_singleton_of_mulEquiv ε]
    exact CFSG.Walter.J1Props.card_centralizer_of_orderOf_eq_two hε
  have hdvd := SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
  rw [hcard, hC] at hdvd
  norm_num at hdvd

end J1

section He

open CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore


theorem he_outer_false_of_lThree {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.He)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  set θ : S ≃* heP := e.trans heEquivP
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
    (MulAut.congr θ σ) (by rw [orderOf_congr, hσ]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  obtain ⟨hCeq, -, hDeq, -, -, -, -, -, hquot, -, -⟩ :=
    ctbh_outer_centralizer_small_action_arithmetic
  let f : fixedSubgroup σ ≃* heOuterC := (((fixedSubgroupCongr θ σ).trans
      (MulEquiv.subgroupCongr (by rw [hx]))).trans
      (fixedSubgroupEquivOfConj x hg heAutU hxg)).trans (MulEquiv.subgroupCongr hCeq.symm)
  have hB : IsComponent (D.map f.toMonoidHom) := LocalCores.isComponent_map_mulEquiv f hD
  have hq : IsQuasisimple (⁅heOuterC, heOuterC⁆ : Subgroup (Equiv.Perm (Fin 8330))) := by
    rw [← hDeq]
    exact ctbh_outer_centralizer_derived_quasisimple.2.1
  have h1 := card_quotient_center_of_isComponent_of_commutator hq hB
  rw [← hDeq, hquot] at h1
  obtain ⟨ψ⟩ := SporadicRefine.nonempty_quotient_center_map_equiv f D
  rw [← Nat.card_congr ψ.toEquiv, hcard] at h1
  norm_num at h1

theorem he_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168)
    (hσD : F4Pilot.FixedCentralizerTwoFree σ D ∨
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D)) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    rcases hσD with hfree | ⟨-, hsmall⟩
    · exact not_mem_range_conj_of_twoFree hna hσ hfree ⟨s, rfl⟩
    · exact SporadicRefine.he_inner_not_twoSmall e hs hD hsmall
  · exact he_outer_false_of_lThree e hσ hin hD hcard

end He

section Suz


theorem suz_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Suz) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (hσD : F4Pilot.FixedCentralizerTwoFree σ D ∨
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D)) : False := by
  have := hS
  have h64 := not_sixtyFour_dvd_card_fixedSubgroup_lThree hD hDm
    (fixedCentralizerTwoSmall_of_lFive_hyp hσD)
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    rcases hσD with hfree | ⟨-, hsmall⟩
    · exact not_mem_range_conj_of_twoFree hna hσ hfree ⟨s, rfl⟩
    · exact SporadicRefine.suz_inner_not_twoSmall e hs hD hsmall
  · rcases SporadicRefine.suz_outer_card_fixedSubgroup e hσ hin with h | h <;>
      rw [h] at h64 <;> norm_num at h64

end Suz

section ON


theorem on_outer_false_of_lThree {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.ON)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (hfree : F4Pilot.FixedCentralizerTwoFree σ D) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := fixedCentralizerTwoSmall_of_twoFree' hfree
  have hN : D.Normal := RankOne.normal_of_isComponent_of_twoSmall hD h2
  have h2D : 2 ∣ Nat.card D :=
    (show 2 ∣ 168 by norm_num).trans
      ((card_of_lieModel_PSL_three_two hDm) ▸ card_quotient_dvd_card _)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2D
  set a : fixedSubgroup σ := (d : fixedSubgroup σ) with ha
  have ha2 : orderOf a = 2 := by rw [ha, Subgroup.orderOf_coe]; exact hd
  have haS : orderOf (a : S) = 2 := by rw [Subgroup.orderOf_coe]; exact ha2
  have hcoreC : CFSG.oddCore (centralizer {a} : Subgroup (fixedSubgroup σ)) = ⊥ :=
    ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      (RankOne.centralizerSingletonInfEquiv _ a).symm
      (RankOne.on_outer_oddCore_eq_bot e hσ hout haS a.2)
  have hKc : Nat.card (centralizer (D : Set (fixedSubgroup σ))) ≤ 2 :=
    RankOne.card_centralizer_le_two_of_oddCore
      (fun U hU hUD => RankOne.card_le_two_of_le_centralizer h2 hU hUD) d.2 hcoreC
  have hcen : centralizer (D : Set (fixedSubgroup σ)) = ⊥ := by
    have hp : IsPGroup 2 (centralizer (D : Set (fixedSubgroup σ))) := by
      have hpos : 0 < Nat.card (centralizer (D : Set (fixedSubgroup σ))) := Nat.card_pos
      rcases (show Nat.card (centralizer (D : Set (fixedSubgroup σ))) = 1 ∨
          Nat.card (centralizer (D : Set (fixedSubgroup σ))) = 2 by omega) with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    have h := hfree ((centralizer (D : Set (fixedSubgroup σ))).map (fixedSubgroup σ).subtype)
      (hp.map _) ?_ (map_subtype_le _)
    · exact (map_eq_bot_iff_of_injective _ (fixedSubgroup σ).subtype_injective).mp h
    · rintro _ ⟨u, hu, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hu d hd)
  have hdvd := RankOne.on_outer_card_dvd e hσ hout haS a.2
  rw [← Nat.card_congr (RankOne.centralizerSingletonInfEquiv _ a).toEquiv] at hdvd
  exact false_of_lThree_of_centralizer_eq_bot hD.1.1 hDm hcen ha2 hdvd

theorem on_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.ON) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1)
    (hσD : F4Pilot.FixedCentralizerTwoFree σ D ∨
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D)) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    rcases hσD with hfree | ⟨-, hsmall⟩
    · exact not_mem_range_conj_of_twoFree hna hσ hfree ⟨s, rfl⟩
    · exact SporadicRefine.on_inner_not_twoSmall e hs hD hsmall
  · exact on_outer_false_of_lThree e hσ hin hD hDm (hσD.resolve_right fun h => hin h.1)

end ON

section HS

open CFSG.Sporadic.SmallOddCore
open CFSG.QuasithinUnique.Id2519.SporHS (hsRows_cases)


theorem hs_false_of_lThree {S : Type} [Group S] (e : S ≃* NativeSporadic.HS) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (h2 : FixedCentralizerTwoSmall σ D) : False := by
  have : Finite S := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨r, hr, ⟨φ⟩⟩ := SporadicRefine.hs_fixedSubgroup_rows e hσ
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hcardC := (hrows r hr).2.2.2.2.1
  have hC : Nat.card (fixedSubgroup σ) = r.centOrder := by
    rw [Nat.card_congr φ.toEquiv, hcardC]
  have h64 := not_sixtyFour_dvd_card_fixedSubgroup_lThree hD hDm h2
  have hdvd := SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
  rw [card_of_lieModel_PSL_three_two hDm, hC] at hdvd
  rw [hC] at h64
  rcases hsRows_cases hr with h | ⟨-, -, h, -⟩ | ⟨-, h⟩ | h <;> rw [h] at hdvd h64
  all_goals first
    | (norm_num at hdvd; done)
    | (norm_num at h64)

end HS

section McL

open CFSG.ComponentClassification.RestrictedStd.Spor (mcl_inner_comps mcl_outer_comps)


theorem mcl_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.McL) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_conj_eq_centralizerOf s)
    obtain ⟨ψ⟩ := mcl_inner_comps e s hs _ (LocalCores.isComponent_map_mulEquiv φ hD)
    obtain ⟨χ⟩ := SporadicRefine.nonempty_quotient_center_map_equiv φ D
    have h1 := Nat.card_congr (χ.trans ψ).toEquiv
    rw [hcard, CFSG.Sporadic.SmallOddCore.card_mclX] at h1
    norm_num at h1
  · have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix
    have h : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 7920 :=
      mcl_outer_comps e σ (by rw [← sq, ← hσ, pow_orderOf_eq_one]) hin _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    obtain ⟨χ⟩ := SporadicRefine.nonempty_quotient_center_map_equiv φ D
    rw [← Nat.card_congr χ.toEquiv, hcard] at h
    norm_num at h

end McL

section HN


theorem hn_false_of_lThree {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.HN) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 168) : False := by
  rcases ComponentClassification.CatLeaf.exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcardB⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    have h := ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds S e u
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB
    rw [hcardB, hcard] at h
    norm_num at h
  · have h := SporadicRefine.hn_outer_card_quotient_center e hσ hout hD
    rw [hcard] at h
    norm_num at h

end HN

end CFSG.SeitzReduction.LinearPilot
