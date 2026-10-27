module

public import Mathlib.Algebra.Group.Defs

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Z2

@[expose] def heisList {Γ : Type*} [Group Γ] (a b c : Γ) : List Γ :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    (List.range 3).map fun k => a ^ i * b ^ j * c ^ k

end CFSG.AGLEmbedding.KFactProofs.M12Z2
