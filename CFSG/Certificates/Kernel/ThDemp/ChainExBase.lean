
module

public import CFSG.Certificates.Kernel.ThDemp.SoundBase
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp

@[expose] public section

namespace CFSG.Certificates.ThDemp

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Chain

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

abbrev Coords := Fin 31 × Fin 30 × Fin 28 × Fin 24 × Fin 16 × Fin 32

def chainProd {G : Type*} [Group G] (t : ℕ → ℕ → G) (y : Coords) : G :=
  t 5 y.2.2.2.2.2 * t 4 y.2.2.2.2.1 * t 3 y.2.2.2.1 * t 2 y.2.2.1 * t 1 y.2.1 * t 0 y.1

end CFSG.Certificates.ThDemp

end
