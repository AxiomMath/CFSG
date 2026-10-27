module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open
open scoped commutatorElement

@[expose] def IsSU43 (B : Type) [Group B] : Prop :=
  CFSG.IsQuasisimple B ∧ Nat.card (center B) = 4 ∧ IsCyclic (center B) ∧
    CFSG.Blueprint.LieModel (B ⧸ center B) .PSU 4 3 1

section Quotient

variable {G : Type} [Group G]

@[expose] def zElt (z : G) : ↥(centralizer ({z} : Set G)) :=
  ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] def zSubgroup (z : G) : Subgroup ↥(centralizer ({z} : Set G)) :=
  zpowers (zElt z)

instance (z : G) : (zSubgroup z).Normal :=
  normal_of_le_center (zpowers_le.mpr (mem_center_iff.mpr fun y =>
    Subtype.ext (y.2 z (Set.mem_singleton z)).symm))

end Quotient

end CFSG.OddStandard.HigherRank.G2Three
