module

public import CFSG.LieType.HighestRoot.CentSpinBasic
public import CFSG.LieType.HighestRoot.Defs

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.LieType.Universal.Spin CFSG.LieType.HighestRoot CliffordAlgebra QuadraticMap

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

theorem longSL2_neg_one_mul_twin (hQ : Q ≠ 0) (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) :
    F.longSL2 hij s t (-1) * F.longSL2 hij s (!t) (-1) = spinGroup.negOne Q hQ := by
  apply Subtype.ext
  rw [spinGroup.coe_negOne]
  have hsq : (F.longSL2 hij s t (-1) * F.longSL2 hij s t (-1) : spinGroup Q) = 1 := by
    rw [← map_mul]
    simp
  have hsq' : ((F.longSL2 hij s t (-1) : spinGroup Q) : CliffordAlgebra Q) *
      ((F.longSL2 hij s t (-1) : spinGroup Q) : CliffordAlgebra Q) = 1 :=
    congrArg Subtype.val hsq
  show ((F.longSL2 hij s t (-1) : spinGroup Q) : CliffordAlgebra Q) *
    ((F.longSL2 hij s (!t) (-1) : spinGroup Q) : CliffordAlgebra Q) = -1
  rw [coe_longSL2_not_neg_one, mul_neg, hsq']

end CFSG.ClassicalInvolution.RouteD.TWU
