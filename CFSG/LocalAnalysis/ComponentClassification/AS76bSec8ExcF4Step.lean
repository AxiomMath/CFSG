module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTorus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Residual
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Two
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Levi
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.SeitzReduction CFSG.SeitzReduction.F4Pilot
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

variable {K : Type} [Field K]

theorem levi_reps_involution
    [Finite K] [CharP K 2] :
    ∀ x ∈ [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]], x * x = 1 ∧ x ≠ 1 := by
  have hsq : ∀ p, f4x K p 1 * f4x K p 1 = 1 := fun p => by
    rw [f4x, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hc1 : Commute (f4x K 32 1) (f4x K 31 1) :=
    commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 32) (q := 31) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 1
  have hc2 : Commute (f4x K 28 1) (f4x K 32 1) :=
    commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 28) (q := 32) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 1
  have hne : ∀ a b : ℕ, 24 ≤ a ∧ a ≤ 47 → 24 ≤ b ∧ b ≤ 47 → a ≠ b →
      height (orbitCertRoot .F4 a) ≤ height (orbitCertRoot .F4 b) →
      f4x K a 1 * f4x K b 1 ≠ 1 := by
    intro a b ha hb hab hh h
    have h1 : f4x K a 1 = f4x K b 1 := by
      rw [← mul_one (f4x K a 1), ← hsq b, ← mul_assoc, h, one_mul]
    exact one_ne_zero (eq_zero_of_f4x_eq ha hb (Ne.symm hab) hh h1)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨Subtype.ext (by simp only [Subgroup.coe_mul, coe_f4Rep_singleton, hsq]; rfl),
      f4Rep_singleton_ne_one 32⟩
  · exact ⟨Subtype.ext (by simp only [Subgroup.coe_mul, coe_f4Rep_singleton, hsq]; rfl),
      f4Rep_singleton_ne_one 31⟩
  · refine ⟨Subtype.ext ?_, fun h => ?_⟩
    · simp only [Subgroup.coe_mul, coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one,
        Subgroup.coe_one]
      calc f4x K 32 1 * f4x K 31 1 * (f4x K 32 1 * f4x K 31 1) =
          f4x K 32 1 * (f4x K 31 1 * f4x K 32 1) * f4x K 31 1 := by group
        _ = 1 := by rw [← hc1.eq, ← mul_assoc, hsq, one_mul, hsq]
    · have h' := congrArg Subtype.val h
      simp only [coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one, Subgroup.coe_one] at h'
      exact hne 31 32 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
        (by decide +kernel) (by rw [← hc1.eq]; exact h')
  · refine ⟨Subtype.ext ?_, fun h => ?_⟩
    · simp only [Subgroup.coe_mul, coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one,
        Subgroup.coe_one]
      calc f4x K 28 1 * f4x K 32 1 * (f4x K 28 1 * f4x K 32 1) =
          f4x K 28 1 * (f4x K 32 1 * f4x K 28 1) * f4x K 32 1 := by group
        _ = 1 := by rw [← hc2.eq, ← mul_assoc, hsq, one_mul, hsq]
    · have h' := congrArg Subtype.val h
      simp only [coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one, Subgroup.coe_one] at h'
      exact hne 28 32 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
        (by decide +kernel) h'


theorem step814_f4
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) :
    Step814 .F4 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | f4 m hm K hK e =>
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hm hK
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have : Finite (ModGL .F4 K) := finite_modGL
    have : Finite (adjointGroup .F4 K) := Subtype.finite
    have hZC : center (adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
    have e₁ : AdjointQuotient .F4 K ≃* adjointGroup .F4 K :=
      (QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_F4
      (S := rankTwoQuot A) (m := m) ⟨⟨Nat.prime_two, hm, rfl⟩, K, inferInstance, inferInstance,
        hK, ⟨e⟩⟩)
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    refine exists_config814_of_torus h32 h33 h4 h34 (ExcModel.f4 m hm K hK e) hA hZA hZC
      (e.trans e₁) hOut (2 ^ m) rfl hq2 (reps := [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31],
        f4Rep K [28, 32]]) classesCover_levi residualMem_levi
      (fun x hx => charTwo_of_involution (levi_reps_involution x hx).1
        (levi_reps_involution x hx).2)
      (fun hq => hz2_levi (by rw [hK, hq])) (fun hq x hx => ?_)
      (fun _ S hS N hNC hNn hN2 => eq_bot_of_normal_centralizer_F4 S hS N hNC hNn hN2)
      (fun h => by simp [ExcModel.IsTrialityFour] at h)
    have hm2 : 2 ≤ m := by
      by_contra h
      have hm1 : m = 1 := by omega
      rw [hm1] at hq
      norm_num at hq
    have h4K : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    exact ⟨_, _, _, _, leviData_levi h4K hm hK x hx, autFix_levi hm2 hK,
      fun L₀ ⟨f⟩ => statedClassicalModel_of_mulEquiv_C3Levi hK f,
      fun h => by simp [ExcModel.IsTrialityFour] at h⟩
  | g2 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
