module

public import CFSG.RankThree.Native.Fi22FiveCentralizers
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Solomon.Coordinator

section Fi22


theorem noOrder65_fi22P : NoOrder 65 ↥fi22P := by
  intro g hg
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlines, -⟩, -, hrec⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine no_order_mul_of_lines (p := 5) (r := 13) hQP (card_eq_of_sylow_subgroupOf hQP hQsyl)
    fi22FiveLine (lines_of_eq hlines) (fun i => ?_) g.2 (by
      rw [Subgroup.orderOf_coe]; exact hg)
  obtain ⟨-, -, hinf, hcard, -⟩ := hrec i
  rw [← hinf, hcard]
  norm_num

theorem noOrder65_Fi22 :
    NoOrder 65 NativeSporadic.Fi22 := fun g hg =>
  noOrder65_fi22P (fi22PermEquiv g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end Fi22

end CFSG.HardMathSupport.Dickson.Sec6.I1431
