module

public import CFSG.GH74.E2.SDExtGeneric
public import CFSG.GH74.E2.Ext2
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public meta import CFSG.GH74.E2.SDExtGeneric
public import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.SD16Cert

public section

namespace CFSG.GH74.E2

open CFSG.Semidihedral

namespace SDW

local instance instDecEqSD16MForCert : DecidableEq SD16M := inferInstance

@[expose] def sd16R : SD16M := modelR 4 (by norm_num)

@[expose] def sd16S : SD16M := modelS 4 (by norm_num)

@[expose] def sd16Nf (a : SD16M) : ℕ × ℕ :=
  ((Multiplicative.toAdd a.left).val, (Multiplicative.toAdd a.right).val)

@[expose] def lstSD : List SD16M :=
  (List.range 8).flatMap fun i => (List.range 2).map fun j => sd16R ^ i * sd16S ^ j

end SDW

end CFSG.GH74.E2
