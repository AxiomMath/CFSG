module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BGeneric
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.Existence.BabyAmbient
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Amalgam CFSG.ComponentClassification.M12Cover



theorem noNormalFour_Eam : NoNormalFour Eam := by
  have hE := CFSG.Monster.B.CTIB.derivedCoverInput_holds
  obtain ⟨hidx, hperf, hcen, hcenL, hc2, -, -, -⟩ := hE
  have hord : orderOf cE' = 2 := by
    rw [← Nat.card_zpowers]
    exact hc2
  have hsq : ∀ z ∈ zpowers cE', z * z = 1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : cE' ^ (2 : ℤ) = 1 := by
      rw [zpow_ofNat]
      exact hord ▸ pow_orderOf_eq_one cE'
    rw [this, one_zpow]
  refine noNormalFour_of_perfect_index_two hperf hidx (fun z hz hzL => ?_) (fun z hz => ?_)
  · apply hsq
    rw [← hcenL]
    refine ⟨⟨z, hz⟩, mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hzL g g.2).symm
  · apply hsq
    rw [← hcen]
    exact mem_center_iff.2 fun g => (hz g).symm

theorem noNormalFour_centralizer_babyRep_one :
    NoNormalFour (centralizer ({babyRep 1} : Set NativeSporadic.B)) := by
  have hs : orderOf (CFSG.Monster.B.CTIB.rs 1) = 2 :=
    CFSG.Monster.B.CTIB.orderOf_two_iff.2
      ⟨CFSG.Monster.B.CTIB.rs_mul_self (by norm_num), CFSG.Monster.B.CTIB.rs_ne_one (by norm_num)⟩
  obtain ⟨-, r1, -⟩ := CFSG.Monster.B.CTIB.native_four_involution_classes
  obtain ⟨Ψ⟩ := CFSG.Monster.B.CTIB.centralizer_equiv_Eam centralizerInput_B
    (CFSG.Monster.B.CTIB.isConj_labelS_of_rank hs r1)
  have hE := noNormalFour_Eam
  have hconv : CFSG.Monster.B.CTIB.iotaEquiv.symm (CFSG.Monster.B.CTIB.rs 1) = babyRep 1 := by
    unfold babyRep
    rfl
  have h1 : NoNormalFour (centralizer ({CFSG.Monster.B.CTIB.rs 1} : Set CFSG.Monster.B.Sbp)) :=
    noNormalFour_of_mulEquiv Ψ.symm hE
  exact @noNormalFour_centralizer_of_mulEquiv CFSG.Monster.B.Sbp NativeSporadic.B _ Units.instGroup
    CFSG.Monster.B.CTIB.iotaEquiv.symm _ _ hconv h1

theorem noNormalFour_centralizer_babyInv_zero {X : NativeSporadic.B} (hX : BabyInv 0 X) :
    NoNormalFour (centralizer ({X} : Set NativeSporadic.B)) :=
  noNormalFour_centralizer_of_isConj
    (babyTableIII.2 0 (babyRep 1) X babyInv_zero_babyRep_one hX)
    noNormalFour_centralizer_babyRep_one

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
