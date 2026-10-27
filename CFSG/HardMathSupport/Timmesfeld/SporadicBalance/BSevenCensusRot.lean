module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint

structure RotSevenData (x y h k : NativeSporadic.B) : Prop where
  pow_x : x ^ 7 = 1
  comm : x * y = y * x
  card : Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.B)) = 7 ^ 2
  hx : h * x * h⁻¹ = y
  hy : h * y * h⁻¹ = x ^ 3 * y ^ 5
  kx : k * x * k⁻¹ = x ^ 6 * y
  ky : k * y * k⁻¹ = x ^ 5 * y

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
