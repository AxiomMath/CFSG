module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBCommDefs
public import CFSG.RankThree.Asc83Table.MatCert
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Open.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
open CFSG.ComponentClassification.RankTwoSporadic.B.Native
open Finset
open scoped Matrix

variable {d : ℕ}

local notation "Mat" d => Matrix (Fin d) (Fin d) (ZMod 2)
local notation "Vec" d => Fin d → ZMod 2

@[expose] def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem bitZ_true : bitZ true = 1 := rfl

@[simp] theorem bitZ_false : bitZ false = 0 := rfl

end CFSG.ComponentClassification.RankTwoSporadic.B
