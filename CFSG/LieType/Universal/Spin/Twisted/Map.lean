module

public import CFSG.LieType.Universal.Spin.Twisted.Frame

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap

variable {Ns Nb : ℕ} {K : Type*} [Field K] {b c : K}

theorem spinGroupMap_comp_twShortRoot
    (f : quadMinus Ns K b c →qᵢ quadMinus Nb K b c)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i : Fin (Ns - 1)} {i' : Fin (Nb - 1)} (s : Bool)
    (hvec : f (minusVec Ns i s) = minusVec Nb i' s)
    (hplane : ∀ p : Fin 2 → K, f (planeVec Ns p) = planeVec Nb p) :
    f.spinGroupMap.comp (twShortRoot Ns hirr i s) =
      twShortRoot Nb hirr i' s := by
  refine MonoidHom.ext fun x => ?_
  rw [← ofAdd_toAdd x]
  apply Subtype.ext
  rw [MonoidHom.comp_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_twShortRoot, coe_twShortRoot, map_add, map_one, map_mul,
    CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι, hplane, hvec]

end CFSG.LieType.Universal.Spin.Twisted
