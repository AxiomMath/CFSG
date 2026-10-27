module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
import all CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Lang.Coordinator

section


theorem twentySeven_dvd_fixedSubgroup_smallRee (a : ℕ) (ha : 1 ≤ a) (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.G2.prime] (hF : Nat.card F = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (α : MulAut (ReeTag.G2.reeGamma F a)) (hα : α ^ p = 1)
    (hαout : α ∉ inner (ReeTag.G2.reeGamma F a)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨b, -, hcard⟩ := card_fixedSubgroup_outer_smallRee a ha F hF hp hp2 α hα hαout
  rw [hcard]
  have h27 : 27 ∣ (3 ^ (2 * b + 1)) ^ 3 := by
    rw [← pow_mul]
    calc 27 = 3 ^ 3 := by norm_num
      _ ∣ 3 ^ ((2 * b + 1) * 3) := pow_dvd_pow 3 (by omega)
  exact (h27.mul_right _).mul_right _


end

end CFSG.HardMathSupport.Malle.E27Lie
