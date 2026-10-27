module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Two
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Aut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

theorem chevalleyExceptionalModel_E7_of_mulEquiv_e8 {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {p f : ℕ} (h : ChevalleyExceptionalModel H .E7 p f) :
    ChevalleyExceptionalModel G .E7 p f := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem leviClassData_e8Reps
    {G : Type} [Group G] {A : Subgroup G} {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) (e : rankTwoQuot A ≃* AdjointQuotient .E8 K) (hq : 2 < 2 ^ m) :
    ∀ x ∈ e8Reps K, ∃ Dl Ql Hl Ll : Subgroup (adjointGroup .E8 K),
      LeviClassData (ExcModel.e8 m hm K hK e) (zx x) Dl Ql Hl Ll := by
  intro x hx
  have hxL : x ∈ e8L K := coe_mem_subsystemGroup_of_mem_e8Reps x hx
  exact ⟨e8D K, e8Q K, e8T K, e8L K, e8_leviData hm hK hq (zx_le_e8L hm hK hq hxL),
    e8_autFix hm hK hq,
    fun _ ⟨f⟩ => chevalleyExceptionalModel_E7_of_mulEquiv_e8 f (e8L_recognition hm hK).2,
    fun h => by simp [ExcModel.IsTrialityFour] at h⟩

theorem step814_e8
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) : Step814 .E8 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | e8 m hm K hK e =>
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hm hK
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have : Finite (ModGL .E8 K) := finite_modGL
    have : Finite (adjointGroup .E8 K) := Subtype.finite
    have hZC : center (adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
    have e₁ : AdjointQuotient .E8 K ≃* adjointGroup .E8 K :=
      (QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_E
      (S := rankTwoQuot A) (Or.inr (Or.inr rfl)) hm ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩)
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact exists_config814_of_torus h32 h33 h4 h34 (ExcModel.e8 m hm K hK e) hA hZA hZC
      (e.trans e₁) hOut (2 ^ m) rfl hq2 (reps := e8Reps K) classesCover_e8Reps
      (residualMem_e8Reps hm hK) charTwo_e8Reps
      (fun hq x hx => Or.inl (card_zx_e8Reps_two (by rw [hK, hq]) x hx))
      (fun hq => leviClassData_e8Reps hm hK e hq)
      (fun _ => EvenOddRadical.centralizerOTwoFree_adjointGroup (Or.inr (Or.inr (Or.inr rfl))))
      (fun h => by simp [ExcModel.IsTrialityFour] at h)
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.E8
