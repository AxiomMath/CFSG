module

public import CFSG.ClassicalInvolution.AschTight.E2StarTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_oddCoreOf [Finite G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (oddCoreOf L : Set G) := fun _ hg =>
  mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hg)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
