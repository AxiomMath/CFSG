module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.Sporadic.SuzOddCore.SylowFusion
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore


theorem b3Phi_suzFiveLine (i : Fin 6) :
    B3Phi 5 (Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨-, -, hrec, hgood, hbad⟩ := R3E_Suz_full_five_centralizer_structures
  obtain ⟨hCeq, hDs, hDnab, -⟩ := hrec i
  have hR : ∀ r ∈ suzT, ∀ q ∈ suzM, r * q * r⁻¹ ∈ suzM := fun r hr q hq =>
    suzT_conj_mem_suzM hr hq
  have hD : (⁅suzFiveC i, suzFiveC i⁆ : Subgroup (Equiv.Perm (Fin 1782))) = suzFiveD i := rfl
  by_cases hg : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
  · obtain ⟨-, hDcard, hcentEq, hcard5⟩ := hgood i hg
    have hcore : GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓ suzT) = ⊥ := by
      rw [← hCeq]
      exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
        (by rw [hD, hDcard]; norm_num) (IsPGroup.of_card (n := 1) (by rw [pow_one, hD, hcentEq]; exact hcard5))
    exact b3Phi_of_oPrime
      (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five suzM_le_suzT hR hcore)
  · have hb : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
      have := i.2
      omega
    obtain ⟨-, hDcard, hcard10⟩ := hbad i hb
    have hle := gLAPPrimeCoreOf_le_inf_centralizer (p := 5) Nat.prime_five
      (commutator_self_le' (suzFiveC i)) (fun g hg d hd => commutator_self_conj_mem hg hd)
      (isQuasisimple_of_simple_subgroup hDs hDnab) (by rw [hD, hDcard]; norm_num)
    rw [hCeq] at hle
    refine b3Phi_inf_of_ambient_dvd_two_mul Nat.prime_five suzM_le_suzT hR hle ?_
    rw [← hCeq, inf_comm, hD, hcard10]

theorem b3Phi_five_suzM :
    ∀ y ∈ suzM, orderOf y = 5 →
      B3Phi 5 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlines, -⟩, -⟩ := R3E_Suz_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact b3Phi_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) suzFiveLine
    (lines_of_eq hlines) b3Phi_suzFiveLine

theorem b3SporPair_Suz_five
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) : B3SporPair .Suz 5 :=
  b3SporPair_of_model_prime Nat.prime_five (by norm_num) hOut ↥suzM
    ⟨suzEquivM.symm.trans (hbr .Suz).some⟩
    (b3Phi_centralizer_of_sub Nat.prime_five suzM b3Phi_five_suzM)

end CFSG.HardMathSupport.Solomon.Coordinator
