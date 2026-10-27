module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier


theorem gLAPPrimeCoreOf_hs100FiveRecord_eq_bot (r : Fin 31) (hr : r = 0 ∨ r = 2 ∨ r = 23) :
    GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({hs100FiveLine r} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R) = ⊥ := by
  obtain ⟨⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC2, -⟩, ⟨hC23, -⟩, ⟨hA0C, hA0n, -, hA0card, -, -, hA0c⟩,
    ⟨hA23C, hA23n, -, hA23card, -, -, hA23c⟩, ⟨hDs, hDnab, hDcard, -, -, hDcard5⟩⟩, -⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  rcases hr with rfl | rfl | rfl
  · rw [← hC0]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup Nat.prime_five hA0C hA0n
      (IsPGroup.of_card (n := 2) (by rw [hA0card]; norm_num)) hA0c
  · have hD2 : (⁅hs100FiveC2, hs100FiveC2⁆ : Subgroup (Equiv.Perm (Fin 100))) = hs100FiveD2 :=
      rfl
    rw [← hC2]
    exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
      (by rw [hD2, hDcard]; norm_num) (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hDcard5))
  · rw [← hC23]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup Nat.prime_five hA23C hA23n
      (IsPGroup.of_card (n := 3) (by rw [hA23card]; norm_num)) hA23c

theorem b3Phi_five_hs100P :
    ∀ y ∈ hs100P, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 100))) ⊓ hs100P) := by
  obtain ⟨⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩, -⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := hs_autModel
  refine b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) hs100FiveLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hr : hs100FiveRecordOf j = 0 ∨ hs100FiveRecordOf j = 2 ∨ hs100FiveRecordOf j = 23 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rw [← hjconj]
  exact b3Phi_conj_of_normalizes Nat.prime_five hM.conj_mem hjR
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
      (gLAPPrimeCoreOf_hs100FiveRecord_eq_bot _ hr)))

theorem b3SporPair_HS_five
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : B3SporPair .HS 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥hs100P
    ⟨hs100Equiv.symm.trans (hbr .HS).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five hs100P b3Phi_five_hs100P)

theorem gLAPPrimeCoreOf_mcl275FiveRecord_eq_bot (r : Fin 31) (hr : r = 0 ∨ r = 1) :
    GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({mcl275FiveLine r} : Set (Equiv.Perm (Fin 275))) ⊓ mcl275R) = ⊥ := by
  obtain ⟨-, ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hA0C, hA0n, -, hA0card, -, -, hA0c⟩,
    ⟨hA1C, hA1n, -, hA1card, -, -, hA1c⟩⟩⟩ := R3E_HS_McL_full_five_centralizer_structures
  rcases hr with rfl | rfl
  · rw [← hC0]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup Nat.prime_five hA0C hA0n
      (IsPGroup.of_card (n := 2) (by rw [hA0card]; norm_num)) hA0c
  · rw [← hC1]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup Nat.prime_five hA1C hA1n
      (IsPGroup.of_card (n := 3) (by rw [hA1card]; norm_num)) hA1c

theorem b3Phi_five_mcl275P :
    ∀ y ∈ mcl275P, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 275))) ⊓ mcl275P) := by
  obtain ⟨-, ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := mcl_autModel
  refine b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) mcl275FiveLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hr : mcl275FiveRecordOf j = 0 ∨ mcl275FiveRecordOf j = 1 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rw [← hjconj]
  exact b3Phi_conj_of_normalizes Nat.prime_five hM.conj_mem hjR
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
      (gLAPPrimeCoreOf_mcl275FiveRecord_eq_bot _ hr)))

theorem b3SporPair_McL_five
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : B3SporPair .McL 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥mcl275P
    ⟨(mclPermEquiv.trans (MulEquiv.subgroupCongr mcl275P_eq.symm)).symm.trans (hbr .McL).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five mcl275P b3Phi_five_mcl275P)

end CFSG.HardMathSupport.Solomon.Coordinator
