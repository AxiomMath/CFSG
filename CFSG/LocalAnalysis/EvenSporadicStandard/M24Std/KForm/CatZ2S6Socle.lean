module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Blueprint

@[expose] def Z2S6Socle (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* alternatingGroup (Fin 8)) ∨ LieModel S .PSU 4 2 1 ∨ LieModel S .PSL 5 2 1 ∨
    LieModel S .PSU 5 2 1 ∨ LieModel S .PSp 2 2 2 ∨ LieModel S .PSU 4 3 1

end CFSG.EvenSporadicStandard.M24Std
