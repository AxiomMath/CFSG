module

public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Solomon.Coordinator

section Suz


theorem noOrder65_suzM : NoOrder 65 ↥suzM := by
  intro g hg
  obtain ⟨⟨hQM, -, -, -, hQsyl⟩, ⟨hlines, -⟩, hrec, hgood, hbad⟩ :=
    R3E_Suz_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine no_order_mul_of_lines (p := 5) (r := 13) hQM (card_eq_of_sylow_subgroupOf hQM hQsyl)
    suzFiveLine (lines_of_eq hlines) (fun i => ?_) g.2 (by
      rw [Subgroup.orderOf_coe]; exact hg)
  have hdvd : Nat.card ↥(Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓
      suzM) ∣ Nat.card ↥(suzFiveC i) := by
    rw [(hrec i).1]
    exact Subgroup.card_dvd_of_le (inf_le_inf_left _ suzM_le_suzT)
  intro h13
  have h := h13.trans hdvd
  by_cases hi : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
  · rw [(hgood i hi).1] at h
    exact absurd h (by norm_num)
  · have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
      have := i.2
      omega
    rw [(hbad i hi').1] at h
    exact absurd h (by norm_num)

theorem noOrder65_Suz :
    NoOrder 65 NativeSporadic.Suz := fun g hg =>
  noOrder65_suzM (suzEquivM g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end Suz

end CFSG.HardMathSupport.Dickson.Sec6.I1431
