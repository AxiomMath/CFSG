module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T6
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

section TD4Distinct


theorem td4NotL3_holds
    : TD4NotL3 := by
  intro G _ _ L hTD hc
  obtain ⟨d1, hv1, hP1, ⟨e1⟩⟩ := CatB.exists_lieIndex hTD
  obtain ⟨d2, hv2, hP2, ⟨e2⟩⟩ := CatB.exists_lieIndex hc
  cases d1 with
  | trialityD4 q1 =>
    cases d2 with
    | A r q2 =>
      rcases r with _ | _ | _ | r
      all_goals first | exact hP2.elim | skip
      have hq2p : q2.p = 2 := hP2.1
      have hk : Even q2.exponent := by
        by_contra hodd
        have hodd' : Odd q2.exponent := Nat.not_even_iff_odd.1 hodd
        have hc2 : q2.card = 2 ^ q2.exponent := by rw [PrimePower.card_def, hq2p]
        have h2 := two_pow_mod_three_odd hodd'
        rw [← hc2] at h2
        have := hP2.2
        omega
      have hk2 : 2 ≤ q2.exponent := by
        have hpos := q2.exponent_pos
        obtain ⟨j, hj⟩ := hk
        omega
      by_cases hq1 : q1.p = 2
      · have c1 : Nat.card (PSimple 3 L) = orderTrialityD4 q1.card :=
          CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q1, hv1⟩ (PSimple 3 L) ⟨e1⟩
        have c2 : Nat.card (PSimple 3 L) = orderA 2 q2.card :=
          CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 2 q2, hv2⟩ (PSimple 3 L) ⟨e2⟩
        have hq1c : q1.card = 2 ^ q1.exponent := by rw [PrimePower.card_def, hq1]
        have hq2c : q2.card = 2 ^ q2.exponent := by rw [PrimePower.card_def, hq2p]
        exact td4_even_ne_A2 q1.exponent_pos hk2 hk
          (by rw [← hq1c, ← hq2c]; exact c1.symm.trans c2)
      · have hdchar : (⟨LieTypeIndex.A 2 q2, hv2⟩ : ValidLieTypeIndex).1.characteristic = 2 := by
          rw [LieTypeIndex.characteristic_A]
          exact hq2p
        exact CatDistinct.td4_odd_not_even catDistinctCtx_holds q1 hv1 hq1 e1 ⟨.A 2 q2, hv2⟩ hdchar e2
    | _ => exact hP2.elim
  | _ => exact hP1.elim

end TD4Distinct

end I91T

end CFSG.LocalAnalysis.GLTheoremA
