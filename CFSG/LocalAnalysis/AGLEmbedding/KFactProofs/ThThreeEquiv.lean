module

public import CFSG.Sporadic.Th.Setup
import all CFSG.Sporadic.Th.Setup

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.Sporadic.Th CFSG.Blueprint

private theorem thEquivJ_val_aux (u : NativeSporadic.Th) :
    (((thEquivJ u : J) : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) =
      u.val.val := rfl

theorem thEquivJ_val (u : NativeSporadic.Th) :
    (((thEquivJ u : J) : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) =
      u.val.val := thEquivJ_val_aux u

end CFSG.AGLEmbedding.R3
