module

public import CFSG.GH74.Uniqueness.SU.SU12Stmts
public import CFSG.GH74.Uniqueness.SU.SU10Setup
public import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.GH74.Uniqueness.SU.SU10Z
public import CFSG.GH74.Uniqueness.SU.SU13TB1Core
public import CFSG.GH74.Uniqueness.SU.SU14Alt
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.GH74.Uniqueness.SU.KInputs2
public import CFSG.GH74.Uniqueness.SU.SU13TB0Syl

public section

namespace CFSG.GH74.Uniqueness.SU.SU12

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.GH74.Uniqueness.SU.SU10
  CFSG.Blueprint

section Basic

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {M : Subgroup G} {z : G}

theorem Hyp22.z_mem (h : Hyp22 S M z) : z ∈ (S : Subgroup G) := h.toHyp21.z_mem

end Basic

end CFSG.GH74.Uniqueness.SU.SU12
