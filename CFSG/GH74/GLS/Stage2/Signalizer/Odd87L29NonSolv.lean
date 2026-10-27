module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilp
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local

section Solvable

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_twoNilp {D : Type} [Group D] [Finite D] (h : TwoNilp D) :
    Group.IsSolvable D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hodd, a, ha⟩ := h
  have hsolN : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hq : IsPGroup 2 (D ⧸ N) := IsPGroup.of_card (n := a) (by
    rw [← Subgroup.index, ha])
  have : Group.IsNilpotent (D ⧸ N) := hq.isNilpotent
  have : Group.IsSolvable (D ⧸ N) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient N

theorem isSolvable_of_hasNormal2Compl {X : Subgroup G} (h : HasNormal2Compl X) :
    Group.IsSolvable ↥X :=
  isSolvable_of_twoNilp ((hasNormal2Compl_iff_twoNilp X).mp h)

end Solvable

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
