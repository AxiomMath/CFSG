module

public import CFSG.GH74.Uniqueness.SU.SU13TA9Elts
public import CFSG.GH74.Uniqueness.SU.SU13TA9P3

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13
  CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

theorem p3part (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    P3Part z (c.elts hπ hz hz1) :=
  ⟨isSylowIn_s₃ hπ c hz hz1⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
