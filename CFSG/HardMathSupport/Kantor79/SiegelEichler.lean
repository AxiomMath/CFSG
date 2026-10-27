module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.HardMathSupport.GuralnickMalle.LongRootGroup

public section

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle CFSG.ClassicalGroups.Orthogonal
open QuadraticMap LinearMap Module

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

theorem siegelEquiv_eq_eichler {Q : QuadraticForm K E} {u w : E} (hu : Q u = 0) (hw : Q w = 0)
    (huw : QuadraticMap.polar Q u w = 0) (c : K) :
    siegelEquiv Q u w hu hw huw c = eichler Q u (c • w) := by
  have huw' : polar Q u (c • w) = 0 := by
    rw [polar_smul_right, huw, smul_zero]
  have hQw' : Q (c • w) = 0 := by
    rw [QuadraticMap.map_smul Q, hw, smul_zero]
  ext x
  change siegelLin Q u w c x = (eichler Q u (c • w)) x
  rw [show (eichler Q u (c • w)) x = x + polar Q x u • (c • w) -
      (polar Q x (c • w) + Q (c • w) * polar Q x u) • u from eichler_apply hu huw' x]
  rw [siegelLin_apply, hQw', polar_smul_right, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  change x + c • (polar Q x w • u) + c • (polar Q x u • w) =
    x + polar Q x u • c • w + (c • polar Q x w + 0 * polar Q x u) • u
  module

end CFSG.HardMathSupport.Kantor79
