module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.ExactLayer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {K K' : Subgroup G}

theorem exactCore_le_centralizer (c : G) (K : Subgroup G) :
    exactCore c K ≤ Subgroup.centralizer ({c} : Set G) :=
  exactCore3_le_centralizer c K

theorem isPGroup_zpowers_of_sq_eq_one (hc : c * c = 1) : IsPGroup 2 (Subgroup.zpowers c) :=
  CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.ExactLayer
