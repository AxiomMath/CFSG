module

public import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem statedScalars_zmod2_eq_bot (ι : Type) [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι

theorem center_statedOmega_quadPlus_zmod2 {n : ℕ} (hn : 3 ≤ n) :
    Subgroup.center (StatedOmega (StatedQuadPlus n (ZMod 2))) = ⊥ := by
  rw [center_statedOmega_quadPlus hn, statedScalars_zmod2_eq_bot, Subgroup.bot_subgroupOf]

theorem center_statedOmega_quadMinus_zmod2 {n : ℕ} (hn : 4 ≤ n) :
    Subgroup.center (StatedOmega (StatedQuadMinus n (ZMod 2) 1 1)) = ⊥ := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  rw [center_statedOmega_quadMinus hn hirr, statedScalars_zmod2_eq_bot,
    Subgroup.bot_subgroupOf]

end CFSG.HardMathSupport.Timmesfeld.Proving
