module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.HS

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.Native
  CFSG.Sporadic.SmallOddCore CFSG.HardMathSupport.Timmesfeld.Coordinator

set_option linter.unusedSectionVars false

section McL


theorem sporadicTwoBalanceFive_McL : SporadicTwoBalanceFive .McL := by
  intro S _ _ hS hnab he
  obtain ⟨eB⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  obtain ⟨e0⟩ := he
  let θ : S ≃* mcl275P := e0.trans (eB.symm.trans mcl275Equiv)
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 :=
    (Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv).le.trans
      outer_card_mcl275P
  obtain ⟨-, ⟨⟨hQP, hQsyl, hQc, hQe⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hC0c⟩, -, -, -⟩⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  have hC0' : Nat.card (Subgroup.centralizer ({mcl275FiveLine 0} : Set (Equiv.Perm (Fin 275))) ⊓
      mcl275R : Subgroup (Equiv.Perm (Fin 275))) < 5 ^ 3 := by
    rw [← hC0, hC0c]
    norm_num
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.isLocallyBalancedAbs_two_of_autModel
    Nat.prime_five (by norm_num) CFSG.RankThree.PartOne.mcl_autModel θ hcen hout
    (CFSG.HardMathSupport.Dickson.LocalTwoBalance.ltbFive_witness_of_lines
      CFSG.RankThree.PartOne.mcl_autModel hQP hQsyl (hQc.trans (by norm_num)) hQe hlines htrans
      (fun j => gLAPPrimeCoreOf_mcl275FiveRecord_eq_bot _
        (CFSG.HardMathSupport.Dickson.LocalTwoBalance.ltbFive_two_of_mem (hrecmem j))) hC0')

end McL

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
