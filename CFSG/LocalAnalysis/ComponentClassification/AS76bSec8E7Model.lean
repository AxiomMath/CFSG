module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Two
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Aut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Sec810
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.RankThree.PartOne.S12K.OrdRigidL
import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Classes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem statedClassicalModel_of_mulEquiv_e7
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) {L : Type} [Group L]
    (e : L ≃* rankTwoQuot (e7L K)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L .POmegaPlus 6 2 m :=
  CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
    (statedClassicalModel_of_lieModel_POmegaPlus (e7L_recognition hm hK).2)

theorem center_SL2_eq_bot_of_charTwo {F : Type} [Field F] [CharP F 2] :
    center SL(2, F) = ⊥ := by
  rw [eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem card_SL2_field {F : Type} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2

theorem isEmpty_mulEquiv_SL2_of_POmegaPlus {G : Type} [Group G] {L₀ : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot L₀) .POmegaPlus 6 2 m)
    (n : ℕ) : IsEmpty (↥L₀ ≃* SL(2, GaloisField 2 n)) := by
  refine ⟨fun e => ?_⟩
  have hZSL := center_SL2_eq_bot_of_charTwo (F := GaloisField 2 n)
  have hZ : center ↥L₀ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ center (SL(2, GaloisField 2 n)) := mem_center_iff.2 fun y => by
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz x]
    rw [hZSL, mem_bot] at hez
    rw [mem_bot]
    exact e.injective (by rw [hez, map_one])
  have hc1 : Nat.card (rankTwoQuot L₀) = Nat.card ↥L₀ :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  have hc2 : Nat.card ↥L₀ = Nat.card (GaloisField 2 n) * (Nat.card (GaloisField 2 n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact card_SL2_field
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  obtain ⟨k, -, hk⟩ := FiniteField.card (GaloisField 2 n) 2
  have hF : Nat.card (GaloisField 2 n) = 2 ^ (k : ℕ) := by
    rw [Nat.card_eq_fintype_card, hk]
  have hc3 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl
  rw [hc1, hc2, hF] at hc3
  have hA := CFSG.RankThree.PartOne.S12K.ordA_one_eq (g := (k : ℕ)) k.pos
  exact CFSG.RankThree.PartOne.S12K.ordD_ne_ordA_one (n := 6) (by norm_num) hm k.pos
    (hc3.symm.trans hA.symm)

theorem leviClassData_e7Reps
    {G : Type} [Group G] {A : Subgroup G} {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) (e : rankTwoQuot A ≃* AdjointQuotient .E7 K) (hq : 2 < 2 ^ m) :
    ∀ x ∈ e7Reps K, ∃ Dl Ql Hl Ll : Subgroup (adjointGroup .E7 K),
      LeviClassData (ExcModel.e7 m hm K hK e) (zx x) Dl Ql Hl Ll := by
  intro x hx
  have hxL : x ∈ e7L K := coe_mem_subsystemGroup_of_mem_e7Reps x hx
  exact ⟨e7D K, e7Q K, e7T K, e7L K, e7_leviData hm hK hq (zx_le_e7L hm hK hq hxL),
    e7_autFix hm hK hq, fun _ ⟨f⟩ => statedClassicalModel_of_mulEquiv_e7 hm hK f,
    fun h => by simp [ExcModel.IsTrialityFour] at h⟩

theorem step814_e7
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h810 : E7Sec810) : Step814 .E7 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | e7 m hm K hK e =>
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hm hK
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have : Finite (ModGL .E7 K) := finite_modGL
    have : Finite (adjointGroup .E7 K) := Subtype.finite
    have hZC : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    have e₁ : AdjointQuotient .E7 K ≃* adjointGroup .E7 K :=
      (QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_E
      (S := rankTwoQuot A) (Or.inr (Or.inl rfl)) hm ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩)
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨R, T, g, hc, hTA, hRA⟩ := h810 G A (ExcModel.e7 m hm K hK e) rfl hA hZA
    exact exists_config814_of_torus_of_sec3 h32 h4 h34 (ExcModel.e7 m hm K hK e) hZA hZC
      (e.trans e₁) hOut (2 ^ m) rfl hq2 (reps := e7Reps K) classesCover_e7Reps charTwo_e7Reps
      (fun hq x hx => Or.inl (card_zx_e7Reps_two (by rw [hK, hq]) x hx))
      (fun hq => leviClassData_e7Reps hm hK e hq)
      (fun _ => EvenOddRadical.centralizerOTwoFree_adjointGroup (Or.inr (Or.inr (Or.inl rfl))))
      (fun h => by simp [ExcModel.IsTrialityFour] at h) hc hTA hRA
      (fun L₀ n hL ⟨f⟩ => ((isEmpty_mulEquiv_SL2_of_POmegaPlus hm hL n).false f).elim)
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
