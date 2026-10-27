module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Assembly

open Subgroup

private noncomputable def toLinEquiv (n : Type*) [Fintype n] [DecidableEq n] (K : Type*)
    [CommRing K] : GL n K ≃* ((n → K) ≃ₗ[K] (n → K)) :=
  (Matrix.GeneralLinearGroup.toLin (n := n) (R := K)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K))

private theorem toLinEquiv_apply {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [CommRing K]
    (g : GL n K) (v : n → K) :
    (toLinEquiv n K g) v = (g : Matrix n n K).mulVec v := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)
      (Matrix.GeneralLinearGroup.toLin (n := n) (R := K) g)) v =
      (g : Matrix n n K).mulVec v
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

end CFSG.Assembly

end

