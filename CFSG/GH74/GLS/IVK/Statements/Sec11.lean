module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def resRep {k : Type} [CommSemiring k] {H : Type} [Group H] {V : Type} [AddCommMonoid V]
    [Module k V] (ρ : Representation k H V) (K : Subgroup H) : Representation k ↥K V :=
  ρ.comp K.subtype

end CFSG.GH74.GLS.IVK
