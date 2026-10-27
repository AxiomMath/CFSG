module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM2Marking
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrderSix
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.Open.OrderForm
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2274
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.StandardType CFSG.StandardType.ChevTwo CFSG.Assembly CFSG.Blueprint TauCeti
open CFSG.Yardstones.Md0ec50421ce4

theorem orderTrialityD4_ne_6048 {m : ℕ} (hm : 2 ≤ m) : CFSG.Open.orderTrialityD4 m ≠ 6048 := by
  unfold CFSG.Open.orderTrialityD4
  have h1 : 2 ^ 12 ≤ m ^ 12 := Nat.pow_le_pow_left hm 12
  have h2' : 63 ≤ m ^ 6 - 1 := by
    have h : 2 ^ 6 ≤ m ^ 6 := Nat.pow_le_pow_left hm 6
    have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [h64] at h
    generalize m ^ 6 = a at h ⊢
    omega
  have h3' : 3 ≤ m ^ 2 - 1 := by
    have h : 2 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4] at h
    generalize m ^ 2 = a at h ⊢
    omega
  have h4 : 1 ≤ m ^ 8 + m ^ 4 + 1 := Nat.le_add_left 1 _
  have key : 2 ^ 12 * 1 * 63 * 3 ≤ m ^ 12 * (m ^ 8 + m ^ 4 + 1) * (m ^ 6 - 1) * (m ^ 2 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h4) h2') h3'
  intro h
  rw [h] at key
  norm_num at key

theorem I2015LieModelFact_holds : CFSG.LocalAnalysis.GLTheoremA.I2015.I2015LieModelFact := by
  intro H _ _ p δ hp hp2 hδp hX hchev hF
  have hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | lie d => exact exists_lieModel_two_of_valid d hi e
    | sporadic _ => exact hi.elim
  · rcases ambiguousChev_two_cases hi with
      ⟨h5, rfl⟩ | ⟨h6, rfl⟩ | ⟨h8, rfl⟩ | ⟨q, hv, hq, rfl⟩ | ⟨q, hv, hq, rfl⟩
    · exact ⟨.PSL, 2, 2, lieModel_psl_two_four_of_alternating_five e⟩
    ·
      exfalso
      have e6 : psimpleOf p H ≃* alternatingGroup (Fin 6) := e
      rcases hF with hF1 | ⟨rfl, hTD4, -⟩
      · exact not_fieldOn_of_marking_n_one hp hp2 (fieldOn_deltaG δ hF1)
          (canon_n_one_of_b2der δ hX e6)
      · obtain ⟨j, hj, ⟨e'⟩⟩ := hTD4
        cases j with
        | cyclic _ _ => exact hj.elim
        | alternating _ _ => exact hj.elim
        | lie idx => exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_mulEquiv_alternating_six hb idx ⟨e'⟩).false e6
        | sporadic _ => exact hj.elim
    · exact ⟨.PSL, 4, 1, lieModel_psl_four_two_of_alternating_eight e⟩
    · exact ⟨.PSL, 3, 1, lieModel_psl_three_two_of_A_one q hv hq e⟩
    ·
      exfalso
      have hPSU : CFSG.Open.StatedClassicalModel (psimpleOf p H) CFSG.Open.StatedLieTag.PSU 3 3 1 :=
        statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e
      rcases hF with hF1 | ⟨rfl, hTD4, -⟩
      · exact not_fieldOn_of_marking_n_one hp hp2 (fieldOn_deltaG δ hF1)
          (canon_n_one_of_g2der δ hX hPSU)
      · obtain ⟨j, hj, ⟨e'⟩⟩ := hTD4
        cases j with
        | cyclic _ _ => exact hj.elim
        | alternating _ _ => exact hj.elim
        | lie idx =>
          obtain ⟨d, hdv⟩ := idx
          cases d with
          | trialityD4 m =>
            have hA : Nat.card (psimpleOf 3 H) = 6048 := by
              rw [hb ⟨.twistedA 2 q, hv⟩ _ ⟨e⟩]
              simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, hq]
              decide
            have hB : Nat.card (psimpleOf 3 H) = CFSG.Open.orderTrialityD4 m.card :=
              hb ⟨.trialityD4 m, hdv⟩ _ ⟨e'⟩
            exact orderTrialityD4_ne_6048 (Nat.succ_le_of_lt m.isPrimePow_card.one_lt)
              (hB.symm.trans hA)
          | _ => exact hj.elim
        | sporadic _ => exact hj.elim

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
