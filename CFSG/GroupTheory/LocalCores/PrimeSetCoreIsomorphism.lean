module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalCores

theorem prime_set_core_isomorphism {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G ≃* H) (π : Set Nat.Primes) : (piCore π G).map f.toMonoidHom = piCore π H :=
  piCore_map_mulEquiv π f

end CFSG.LocalCores
