module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscE184Graph
public import CFSG.ClassicalInvolution.AschTight.S1916F1
public import CFSG.ClassicalInvolution.Q3.TL4D4NCOne
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

section Norm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H Y : Subgroup G}

@[expose] def restrictGood (Ω : Set (Subgroup G)) (Y K : Subgroup G) (L : Subgroup ↥Y) : Prop :=
  ∃ J ∈ Ω, J ≤ Y ∧ L = J.subgroupOf Y ∧ J ∈ dstarComp Ω K

theorem restrictGood_step {K : Subgroup G} {L L' : Subgroup ↥Y}
    (hL' : L' ∈ restrictFamily Ω Y) (hgood : restrictGood Ω Y K L)
    (hadj : dstarAdj (restrictFamily Ω Y) L L') : restrictGood Ω Y K L' := by
  obtain ⟨J, hJ, hJY, rfl, hJK⟩ := hgood
  obtain ⟨J', hJ', hJ'Y, rfl⟩ := hL'
  have h1 := dstarAdj_map hadj
  rw [Subgroup.map_subgroupOf_eq_of_le hJY, Subgroup.map_subgroupOf_eq_of_le hJ'Y] at h1
  exact ⟨J', hJ', hJ'Y, rfl, hJK.tail h1⟩

end Norm

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
