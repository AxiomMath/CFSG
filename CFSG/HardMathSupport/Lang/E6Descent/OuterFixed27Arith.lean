module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Arith27
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Open CFSG.SeitzReduction.E6Pilot

theorem eightyOne_dvd_numTwistedE6 (q : ℕ) (hq : 1 ≤ q) : 81 ∣ numTwistedE6 q := by
  unfold numTwistedE6
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  generalize (q : ZMod 81) = x
  revert x
  decide +kernel

theorem twentySeven_dvd_ordE6 (q : ℕ) (hq : 1 ≤ q) : 27 ∣ ordE6 q := by
  have h : 81 ∣ ordE6 q * Nat.gcd 3 (q - 1) := by
    rw [ordE6_mul_gcd]
    exact CFSG.HardMathSupport.Malle.E27Lie.eightyOne_dvd_numE6 q hq
  have h3 : ordE6 q * Nat.gcd 3 (q - 1) ∣ ordE6 q * 3 :=
    Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left 3 _)
  have := h.trans h3
  rwa [show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_right (by norm_num)] at this

end CFSG.HardMathSupport.Lang.E6Descent
