module

public import CFSG.ClassicalInvolution.Q3.Q3ZADefs
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z


structure Ctx (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) :
    Prop where
  nab : ∃ x y : G, x * y ≠ y * x
  setup : Q3W.RouteD3Setup K z
  shape : Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z
  odd3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z

@[expose] def TriangleExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Ctx G K z → Nonempty (SymTri G (conjClass3 K))

@[expose] def HeisAtTheorem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Ctx G K z → ∀ θA θB θX : StatedSp 2 F3 →* G, LayerTriple (conjClass3 K) θA θB θX →
      HeisAt θA θB θX ∨ HeisAt θA θB (θX.comp iotaHom)

end CFSG.ClassicalInvolution.Q3.Q3ZA
