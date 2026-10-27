module

import CFSG.ClassicalInvolution.Q3.TL3S8BC8
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3
public import CFSG.ClassicalInvolution.Q3.Q3T6MainData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section C8

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem exists_mul_eq_of_mem_A {a : G} (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ ∃ w ∈ W ⊓ Subgroup.centralizer
      (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
        a * w⁻¹ ∈ Subgroup.centralizer (RL : Set G) :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.exists_mul_eq_of_mem_A hd.toTL3 haS haC hat

end Sec19DataT3

end C8

end CFSG.ClassicalInvolution.Q3.Q3T6
