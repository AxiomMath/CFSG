module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.PartOne.KS.HeFiveCentralizers
public import CFSG.RankThree.PartOne.KS.HeSevenCentralizers
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.HeldB


section Five


theorem gLAPPrimeCoreOf_heFiveRecord_eq_bot :
    GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({heFiveLine 0} : Set (Equiv.Perm (Fin 8330))) ⊓ heAutGroup) = ⊥ := by
  obtain ⟨-, -, -, -, ⟨hC0, -⟩, ⟨hDs, hDnab, hDcard, -, -, hDcard5⟩⟩ :=
    R3E_He_full_five_centralizer_structures
  have hD : (⁅heFiveC0, heFiveC0⁆ : Subgroup (Equiv.Perm (Fin 8330))) = heFiveD0 := rfl
  rw [← hC0]
  exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
    (by rw [hD, hDcard]; norm_num) (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hDcard5))

theorem b3Phi_five_heP :
    ∀ y ∈ heP, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec, -⟩ :=
    R3E_He_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := heAutModel
  refine b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) heFiveLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨hjR, hjconj⟩ := htrans j
  rw [← hjconj, hrec j]
  exact b3Phi_conj_of_normalizes Nat.prime_five hM.conj_mem hjR
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
      gLAPPrimeCoreOf_heFiveRecord_eq_bot))

theorem b3SporPair_He_five (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .He 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥heP
    ⟨heEquivP.symm.trans (hbr .He).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five heP b3Phi_five_heP)

end Five

section Seven


theorem gLAPPrimeCoreOf_heSevenRecord_eq_bot (r : Fin 57) (hr : r = 0 ∨ r = 1 ∨ r = 2) :
    GLAPPrimeCoreOf 7
      (Subgroup.centralizer ({heSevenLine r} : Set (Equiv.Perm (Fin 8330))) ⊓ heAutGroup) = ⊥ := by
  obtain ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hC2, -⟩, ⟨hA0C, hA0n, -, hA0card, -, -, hA0c⟩,
    ⟨hDs, hDnab, hDcard, -, -, hDcard7⟩, ⟨hA2C, hA2n, -, hA2card, -, hA2c⟩⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hp7 : Nat.Prime 7 := by norm_num
  rcases hr with rfl | rfl | rfl
  · rw [← hC0]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup hp7 hA0C hA0n
      (IsPGroup.of_card (n := 3) (by rw [hA0card]; norm_num)) hA0c
  · have hD : (⁅heSevenC1, heSevenC1⁆ : Subgroup (Equiv.Perm (Fin 8330))) = heSevenD1 := rfl
    rw [← hC1]
    exact gLAPPrimeCoreOf_eq_bot_of_record_derived hp7 hDs hDnab
      (by rw [hD, hDcard]; norm_num) (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hDcard7))
  · rw [← hC2]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup hp7 hA2C hA2n
      (IsPGroup.of_card (n := 2) (by rw [hA2card]; norm_num)) hA2c

theorem b3Phi_seven_heP :
    ∀ y ∈ heP, orderOf y = 7 →
      B3Phi 7 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hp7 : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  have hM := heAutModel
  refine b3Phi_of_lines hp7 hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) heSevenLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hr : heSevenRecordOf j = 0 ∨ heSevenRecordOf j = 1 ∨ heSevenRecordOf j = 2 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rw [← hjconj]
  exact b3Phi_conj_of_normalizes hp7 hM.conj_mem hjR
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_inf_eq_bot_of_ambient hp7 hM.le hM.conj_mem
      (gLAPPrimeCoreOf_heSevenRecord_eq_bot _ hr)))

theorem b3SporPair_He_seven (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .He 7 :=
  b3SporPair_of_model_prime (by norm_num) (by norm_num) hOut ↥heP
    ⟨heEquivP.symm.trans (hbr .He).some⟩
    (b3Phi_centralizer_of_sub (by norm_num) heP b3Phi_seven_heP)

end Seven

end CFSG.HardMathSupport.Solomon.Coordinator
