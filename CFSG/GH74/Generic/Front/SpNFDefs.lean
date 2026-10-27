module

public import CFSG.GH74.Generic.Front.SpLA

public section

namespace CFSG.GH74.Generic

open Matrix

@[expose] def TensorNF {F : Type} [Field F] (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : Prop :=
  ∃ (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (a G : Matrix (Fin 2) (Fin 2) F),
    IsUnit P.det ∧ A * P = P * fromBlocks a 0 0 a ∧
      Pᵀ * sp2Gram F * P = fromBlocks 0 G (-G) 0

end CFSG.GH74.Generic
