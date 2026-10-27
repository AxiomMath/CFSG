module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LieType.Chevalley.LatticeCharacterInterpolation
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ordE6_mul_gcd (q : ℕ) :
    CFSG.Open.ordE6 q * Nat.gcd 3 (q - 1) = lieOrderNumerator .E6 0 q := by
  unfold CFSG.Open.ordE6
  rw [lieOrderNumerator]
  refine Nat.div_mul_cancel ?_
  refine Dvd.dvd.mul_left ?_ _
  exact (Nat.gcd_dvd_right 3 (q - 1)).trans (Nat.sub_one_dvd_pow_sub_one q 2)

end CFSG.HardMathSupport.Lang.Coordinator
