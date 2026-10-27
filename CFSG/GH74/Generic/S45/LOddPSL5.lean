module

public import CFSG.GH74.Generic.S45.LLinSel
public import CFSG.GH74.Generic.S45.LOddG

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank

theorem oddRow_psl_ge_five {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) {r f m : ℕ} (hr2 : r ≠ 2) (hm : 5 ≤ m)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSL m r f) : False := by
  obtain ⟨yb, Lb, q, -, hQ, -⟩ := hyp.quot_data
  exact psl_ge_five_false hyp.1.1.2.1 hyp.1.1.2.2 hr2 hm hmodel hQ

theorem oddRowG_PSL5 : OddRowG_PSL5 :=
  fun _ _ _ _ _ hypg _ _ hr2 _ hmodel => oddRow_psl_ge_five hypg.2 hr2 (by norm_num) hmodel

end CFSG.GH74.Generic.S45
