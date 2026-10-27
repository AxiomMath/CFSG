module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalSporadicL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInvol
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCent
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalComponent
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalEnd
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStandard
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalMultipliers
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalMultipliersSuz
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFEven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenOut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECMult
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZEnd

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exc_of_four_dvd_tableOrder {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (h4 : 4 ∣ L34Facts.EvenCover.tableOrder t n 2 f) :
    (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
      (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨ (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨
      (t = .PSL ∧ n = 3 ∧ f = 2) := by
  unfold L34Facts.EvenCover.tableOrder at h4
  have hg := L34Facts.EvenCover.not_two_dvd_generic hadm
  have hcop : Nat.Coprime 4 ((genericOrders t n 2 f).1 * (genericOrders t n 2 f).2) := by
    have h2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg
    have := Nat.Coprime.pow_left 2 h2
    norm_num at this
    exact this
  have he := hcop.dvd_of_dvd_mul_left h4
  unfold exceptionalOrders at he
  split at he <;> simp_all

theorem centreTwoPartLe_two_of_classical (hGA : TBLit.GriessMultipliersAllModels) {X : Type}
    [Group X] {τ : StatedLieTag} {n f : ℕ} (hτ : τ ∈ classicalTags) (hX : LieModel X τ n 2 f)
    (hne : ¬ ((τ = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨ (τ = .PSU ∧ n = 6 ∧ f = 1) ∨
      (τ = .PSL ∧ n = 3 ∧ f = 2))) :
    CentreTwoPartLe X 2 := by
  intro L _ _ hq he T
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : LieModel (L ⧸ center L) τ n 2 f := LieType.CurtisTits.lieModel_of_mulEquiv e.symm hX
  have hadm := LieType.Steinberg.CentralExt.GriessNative.admissible_of_lieModel hmodel
  have hdvd := L34Facts.EvenCover.card_center_dvd_tableOrder hq
    (L34Facts.EvenCover.griessRow_of_classical hGA hmodel hτ)
  have hT := (Subgroup.card_subgroup_dvd_card (T : Subgroup (center L))).trans hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (T.isPGroup' : IsPGroup 2 T)
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> simp_all
  have h4 : 4 ∣ Nat.card T := by
    rw [hk]
    exact (show (4 : ℕ) ∣ 2 ^ 2 by norm_num).trans (pow_dvd_pow 2 hk2)
  rcases exc_of_four_dvd_tableOrder hadm (h4.trans hT) with h | h | h | h | h
  · exact hne (Or.inl h)
  · exact hne (Or.inr (Or.inl h))
  · exact absurd hτ (by rw [h.1]; decide)
  · exact absurd hτ (by rw [h.1]; decide)
  · exact hne (Or.inr (Or.inr h))

theorem centreRow_of_evenLie
    (hGA : TBLit.GriessMultipliersAllModels) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hL34 : IsL34Type (P ⧸ Open.fusionZStar P)) : L34CentreRow S P := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · rcases hU with ho | ⟨n, -, h7, hA⟩ | hL | hH
      · exact absurd hL34 (not_held_not_L34_of_properFixedComponent_oddLie
          gls3OddLieAutComponentsInput_holds CatLeafProof.lieOrderFormulasInput hna ho h).2
      · obtain ⟨θ⟩ := hA
        exact absurd hL34 (not_isL34Type_of_properFixedComponent_alternating (by omega) θ h)
      · exact (L34PF.false_of_isL34Type_self h hL34 hL).elim
      · obtain ⟨eHe⟩ := hH
        exact Or.inl fun L _ _ hq he T => centreTwoPartLe_he
          Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate L hq
          (he.map fun e' => e'.trans eHe) T
  · obtain ⟨τ, n, f, hadm, hm⟩ := heven
    by_cases hτ : τ ∈ classicalTags
    · by_cases hexc : (τ = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨ (τ = .PSU ∧ n = 6 ∧ f = 1) ∨
          (τ = .PSL ∧ n = 3 ∧ f = 2)
      ·
        exfalso
        obtain ⟨eP⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
        have hL' : IsL34Type (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
            Open.fusionZStar ↥(P.subgroupOf (fixedSubgroup σ))) :=
          LieType.CurtisTits.lieModel_of_mulEquiv eP hL34
        rcases hexc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact evenLieExcOuterL34Input_holds S .POmegaPlus 4 1 (by simp) hm σ hσ2 hout _
            h.2.2.1 hL'
        · exact evenLieExcOuterL34Input_holds S .PSU 6 1 (by simp) hm σ hσ2 hout _ h.2.2.1 hL'
        · exact L34PF.false_of_isL34Type_self h hL34 hm
      ·
        have eP := subgroupOfEquivOfLe h.2.1
        have hd : 20160 ∣ Nat.card ↥(P.subgroupOf (fixedSubgroup σ)) := by
          rw [Nat.card_congr eP.toEquiv]
          exact L34PF.dvd_card_of_isL34Type hL34
        have hs := L34PF.isSimpleGroup_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 hd
        have : IsSimpleGroup P := eP.symm.isSimpleGroup
        have hnaP : ∃ a b : P, a * b ≠ b * a := HeldBalSpor.exists_mul_ne_mul_of_four_dvd
          ((show 4 ∣ 20160 by norm_num).trans (L34PF.dvd_card_of_isL34Type hL34))
        refine Or.inr (Or.inl ⟨?_, centreTwoPartLe_two_of_classical hGA hτ hm hexc⟩)
        rw [center_eq_bot_of_simple hnaP, Subgroup.card_bot]
    · exfalso
      have hτ' : τ ≠ .PSL ∧ τ ≠ .PSU ∧ τ ≠ .PSp ∧ τ ≠ .POmegaOdd ∧ τ ≠ .POmegaPlus ∧
          τ ≠ .POmegaMinus := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hτ (by decide)
      obtain ⟨eP⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
      exact L34R.not_isL34Type_outer_nonclassical CatLeafProof.lieOrderFormulasInput hτ' hadm
        hm hσ2 hout h.2.2.1 (LieType.CurtisTits.lieModel_of_mulEquiv eP hL34)

section Rows

theorem l34CentreRows_holds : L34CentreRows := by
  intro S _ _ hs hna hcat σ P h hL34
  have : IsSimpleGroup S := hs
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, hA⟩ | ho | he | hsp
  · obtain ⟨θ⟩ := hA
    exact absurd hL34 (not_isL34Type_of_properFixedComponent_alternating hn θ h)
  · exact absurd hL34 (not_held_not_L34_of_properFixedComponent_oddLie
      gls3OddLieAutComponentsInput_holds CatLeafProof.lieOrderFormulasInput hna ho h).2
  · exact centreRow_of_evenLie HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      hna he h hL34
  · rcases HeldBalSpor.sporadicL34ComponentsInput_holds S hs hsp σ P h hL34 with
      ⟨hSuz, hZP⟩ | ⟨-, hZP4⟩ | hHe
    · obtain ⟨e⟩ := hSuz
      exact Or.inr (Or.inl ⟨hZP, fun L _ _ hq he T =>
        centreTwoPartLe_suz_cert L hq (he.map fun e' => e'.trans e) T⟩)
    · exact Or.inr (Or.inr hZP4)
    · obtain ⟨e⟩ := hHe
      exact Or.inl fun L _ _ hq he T => centreTwoPartLe_he
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate L hq
        (he.map fun e' => e'.trans e) T

theorem heldKStableCentre_holds : HeldKStableCentre :=
  heldKStableCentre_of_centreRows l34CentreRows_holds fun _ _ h => card_of_isL34Type h

end Rows

section Balanced

theorem heStandardBalanced_of_heldKSwapped (hP2 : HeldKSwapped) :
    OddStandard.HeStandardBalanced :=
  heStandardBalanced_of_heldEndStepBal
      (heldEndStepBal_of_steps
          (heldKNormalStepBal_of_inputs heldTwoALayerFact heldTwoAKFact heldInvolAutFact
              L34Facts.l34InvolutionCentralizerFact
              (heldKComponentStepBal_of_P1_P2 heldTwoALayerFact heldTwoAKFact
                  heldKStableCentre_holds hP2))
          (heldZStarEndStep_of_facts heldOuterSolvableFact heldInvolAutFact heldTwoAKFact
              heldTwoBFact heldSylowFourFact heldTwoALayerFact
              (heldTwoAFourFact_of_model HeGS.heldTwoAFourModel)
              (heldTwoBCentralizerFact_of_model HeGS.heldTwoBTwelveModel)
              (heldTwoAPairFact_of_model HeGS.heldTwoAPairModel)
              (heldTwoAGenerationFact_of_model HeGS.heldTwoAGenerationModel))
          (heldTwoBCentralizerFact_of_model HeGS.heldTwoBTwelveModel) heldTwoALayerFact
          (heldTwoAFourFact_of_model HeGS.heldTwoAFourModel) heldTwoAClassFact
          (heldTwoAPairFact_of_model HeGS.heldTwoAPairModel)
          (heldTwoAGenerationFact_of_model HeGS.heldTwoAGenerationModel))

end Balanced

end CFSG.ComponentClassification.GrSLit
