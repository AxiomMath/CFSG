module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.PartOne.KS.RuFiveCentralizers
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier


theorem gLAPPrimeCoreOf_ruFiveRecord_eq_bot (r : Fin 31) (hr : r = 0 ∨ r = 1) :
    GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({ruFiveLine r} : Set (Equiv.Perm (Fin 4060))) ⊓ ruP) = ⊥ := by
  obtain ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hAC, hAn, -, hAcard, -, -, hAc⟩,
    ⟨hDs, hDnab, hDcard, -, -, hDcard5⟩⟩ := R3E_Ru_full_five_centralizer_structures
  rcases hr with rfl | rfl
  · rw [← hC0]
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup Nat.prime_five hAC hAn
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  · have hD : (⁅ruFiveC1, ruFiveC1⁆ : Subgroup (Equiv.Perm (Fin 4060))) = ruFiveD1 := rfl
    rw [← hC1]
    exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
      (by rw [hD, hDcard]; norm_num) (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hDcard5))

theorem b3Phi_five_ruP :
    ∀ y ∈ ruP, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 4060))) ⊓ ruP) := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩ :=
    R3E_Ru_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) ruFiveLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨hjP, hjconj⟩ := htrans j
  have hr : ruFiveRecordOf j = 0 ∨ ruFiveRecordOf j = 1 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rw [← hjconj]
  exact b3Phi_conj_of_normalizes Nat.prime_five
    (fun r hr q hq => ruP.mul_mem (ruP.mul_mem hr hq) (ruP.inv_mem hr)) hjP
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_ruFiveRecord_eq_bot _ hr))

theorem b3SporPair_Ru_five (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .Ru 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥ruP
    ⟨ruEquivP.symm.trans (hbr .Ru).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five ruP b3Phi_five_ruP)

end CFSG.HardMathSupport.Solomon.Coordinator
