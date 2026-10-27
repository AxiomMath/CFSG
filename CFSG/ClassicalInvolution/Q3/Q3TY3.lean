module

public import CFSG.ClassicalInvolution.Q3.Q3WShape
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.Assembly.LowTwoRank (StatedLieTag)


@[expose] def TwinLinked3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      (t = .PSp ∧ n = 2) ∨ (t = .PSU ∧ n = 4) →
      LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
      ∀ K₂ ∈ centralizingMembers (conjClass3 K) {z}, K₂ ≠ K →
        (∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T) →
        ∀ w : G, IsClassicalMember3 K₂ w → LinkedAtProduct (conjClass3 K) K z w

end CFSG.ClassicalInvolution.Q3.Q3TY
