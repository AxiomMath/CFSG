module

public import CFSG.ThirdParty.TauCeti.DiagonalizableCentralizerTangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)] {X : Type w} [CommGroup X]

local notation "kX" => MonoidAlgebra k X
local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

end CFSG.LieType.AlgebraicGroups
