module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.Native.Co3FiveCentralizers
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3


theorem gLAPPrimeCoreOf_co3FiveRecord_eq_bot (r : Fin 31) (hr : r = 0 ∨ r = 25) :
    GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({co3FiveLine r} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) = ⊥ := by
  obtain ⟨-, -, -, -, -, hC0, -, hDs, hDnab, hDcard, -, hDcard5, hC25, -, hAC, hAn, hAcard, -, -,
    hAc⟩ := R3E_Co3_full_five_centralizer_structures
  rcases hr with rfl | rfl
  · have hD : (⁅co3FiveC0, co3FiveC0⁆ : Subgroup (Equiv.Perm (Fin 276))) = co3FiveD := rfl
    rw [← hC0]
    exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
      (by rw [hD, hDcard]; norm_num) (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hDcard5))
  · rw [← hC25]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup Nat.prime_five hAC hAn
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc

theorem b3Phi_five_co3P :
    ∀ y ∈ co3P, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec0, hrec25, -⟩ :=
    R3E_Co3_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) co3FiveLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨hjP, hjconj⟩ := htrans j
  have hr : co3FiveRecordOf j = 0 ∨ co3FiveRecordOf j = 25 := by
    by_cases h : (j : ℕ) = 25
    · exact Or.inr ((hrec25 j).2 h)
    · exact Or.inl ((hrec0 j).2 h)
  rw [← hjconj]
  exact b3Phi_conj_of_normalizes Nat.prime_five
    (fun r hr q hq => co3P.mul_mem (co3P.mul_mem hr hq) (co3P.inv_mem hr)) hjP
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_co3FiveRecord_eq_bot _ hr))

theorem b3SporPair_Co3_five (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .Co3 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥co3P
    ⟨co3PermEquiv.symm.trans (hbr .Co3).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five co3P b3Phi_five_co3P)

end CFSG.HardMathSupport.Solomon.Coordinator
