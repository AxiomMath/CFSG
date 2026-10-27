
module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.Checks3
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.KGroups.L34Base
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.GH74.KGroups.L34Base
public import CFSG.GH74.KGroups.CoverL34Inputs
public meta import CFSG.GH74.KGroups.CoverL34Inputs
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.KGroups.L34Inputs

@[expose] public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem gens_mem : ∀ g ∈ [PA, PB], g ∈ QP.originalSubgroup := by
  intro g hg
  rw [QP_closure]
  apply Subgroup.subset_closure
  simpa using hg

end CFSG.GH74.KGroups.L34
