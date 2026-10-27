module

public import CFSG.ClassicalInvolution.Q3.Q3T6BTwinP

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

section Twins

variable {K J : Subgroup F} {t z : F}

theorem oddCoreOf_eq_oddCoreIn {L : Subgroup F} {a : F} (hL : Mem3 L a) :
    oddCoreOf L = Balance.oddCoreIn (Subgroup.centralizer ({a} : Set F)) :=
  Uniform.oddCoreIn_eq_of_intrinsic hL.member (hL.intrinsic solvableType_three)

theorem twinProd_le_centralizer' (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k) :
    twinProd K J ≤ Subgroup.centralizer ({t} : Set F) :=
  iSup₂_le fun _ hL => (mem3_of_mem_twinClass hJ htK hL).le_centralizer

end Twins

end CFSG.ClassicalInvolution.Q3.Q3T6Y
