module

public import CFSG.GH74.Generic.S45.LPsuCover

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.Assembly.LowTwoRank

theorem oddRow_psu3 {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSU 3 r f) : False := by
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  obtain ⟨F, _, h, θ, τ, c, hθ, hτ, hc, hord⟩ := psu_fixed_data (n := 3) (by norm_num) hr2 hmodel
    (fun h A l hAu hAA hNl => Uni.class1b_odd h (by decide) (Uni.two_ne_zero_of_ne h hr2) A l hAu
      hAA hNl)
    (fun h A hAu hAA => Uni.class2alt_odd h (by decide) (Uni.two_ne_zero_of_ne h hr2) A hAu hAA)
    hQ.sq
  exact hyp.false_of_su_fixed hyb h hr2 (by norm_num) θ hθ τ hτ c hc hord

theorem oddRowG_PSU3 : OddRowG_PSU3 :=
  fun _ _ _ _ _ hypg _ _ hr2 hmodel => oddRow_psu3 hypg.2 hr2 hmodel

end CFSG.GH74.Generic.S45
