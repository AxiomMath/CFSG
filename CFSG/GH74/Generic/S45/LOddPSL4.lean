module

public import CFSG.GH74.Generic.S45.LLinFour
public import CFSG.GH74.Generic.S45.LSymGraph
public import CFSG.GH74.Generic.S45.LOddG

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank

theorem oddRow_psl4 {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSL 4 r f) : False := by
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  obtain ⟨F, _, _, hk, ψ, B, hB, hψ⟩ :=
    psl_four_symm_or_false hyp.1.1.2.1 hyp.1.1.2.2 hr2 hmodel hQ
  exact hyp.false_of_symmetric_graph hyb hk (by norm_num) ψ B hB hψ

theorem oddRowG_PSL4 : OddRowG_PSL4 :=
  fun _ _ _ _ _ hypg _ _ hr2 _ hmodel => oddRow_psl4 hypg.2 hr2 hmodel

end CFSG.GH74.Generic.S45
