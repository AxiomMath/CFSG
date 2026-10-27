module

public import CFSG.GH74.SmallRanks.Basic
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.GH74.SmallRanks.PSU3
public import CFSG.GH74.SmallRanks.AltM11

public section

namespace CFSG.GH74

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem twoRank_le_two_of_lieModel_PSL_two_odd {G : Type} [Group G] [Finite G] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : Blueprint.LieModel G .PSL 2 p f) :
    CFSG.Open.twoRank G ≤ 2 :=
  SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem twoRank_eq_of_lieModel_PSL_two_two {G : Type} [Group G] [Finite G] {f : ℕ}
    (h : Blueprint.LieModel G .PSL 2 2 f) : CFSG.Open.twoRank G = f :=
  SmallRanks.twoRank_eq_of_statedClassicalModel_PSL_two_two
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem twoRank_le_two_of_lieModel_PSL_three_three {G : Type} [Group G] [Finite G]
    (h : Blueprint.LieModel G .PSL 3 3 1) : CFSG.Open.twoRank G ≤ 2 :=
  SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_three_three
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem twoRank_le_two_of_lieModel_PSU_three_three {G : Type} [Group G] [Finite G]
    (h : Blueprint.LieModel G .PSU 3 3 1) : CFSG.Open.twoRank G ≤ 2 :=
  SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_three
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem twoRank_le_two_of_lieModel_PSU_three_four {G : Type} [Group G] [Finite G]
    (h : Blueprint.LieModel G .PSU 3 2 2) : CFSG.Open.twoRank G ≤ 2 :=
  SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_four
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem twoRank_le_two_of_alternating_seven {G : Type} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 7)) : CFSG.Open.twoRank G ≤ 2 := by
  rw [twoRank_eq_of_mulEquiv e]
  exact SmallRanks.twoRank_alternatingGroup_seven_le_two

theorem twoRank_le_two_of_M11 {G : Type} [Group G] [Finite G]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .M11) : CFSG.Open.twoRank G ≤ 2 := by
  obtain ⟨e⟩ := h
  have e' : G ≃* CFSG.Blueprint.NativeSporadic.M11 := e
  have : Finite CFSG.Blueprint.NativeSporadic.M11 := Finite.of_equiv G e'.toEquiv
  rw [twoRank_eq_of_mulEquiv e']
  exact SmallRanks.twoRank_M11_le_two

end CFSG.GH74
