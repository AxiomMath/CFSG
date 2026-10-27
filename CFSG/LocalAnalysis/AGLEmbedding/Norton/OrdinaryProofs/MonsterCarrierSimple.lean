module

public import CFSG.Open.MonsterY443Finiteness
public import CFSG.Sporadic.Bridge.Y443Relabel

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

theorem carrier_M_simple :
    IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
  have : IsSimpleGroup CFSG.Open.MonsterY443Derived :=
    CFSG.Open.Open.monster_y443_derived_simple
  exact MulEquiv.isSimpleGroup CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
