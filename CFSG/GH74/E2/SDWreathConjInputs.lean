module

public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public meta import CFSG.GH74.E2.Ext2
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Defs
public import CFSG.GH74.E2.Ext2
public import CFSG.GH74.E2.SD16Cert

public section

namespace CFSG.GH74.E2

open Subgroup
namespace SDW

local instance instDecEqSD16MForConj : DecidableEq SD16M := inferInstance

end SDW

end CFSG.GH74.E2
