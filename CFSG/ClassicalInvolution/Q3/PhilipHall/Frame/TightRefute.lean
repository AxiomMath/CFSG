module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TL3LeafCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

private theorem isPGroup_zpowers_of_isPGroup {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : IsPGroup 2 R) {x : G} (hx : x ∈ R) : IsPGroup 2 (Subgroup.zpowers x) := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
  refine IsPGroup.of_card_dvd_pow (n := m) ?_
  rw [← hm]
  exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)

theorem tightCore_eq_of_isPGroup {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : IsPGroup 2 R) : tightCore R = R := by
  refine le_antisymm (tightCore_le R) fun x hx => ?_
  exact Subgroup.subset_closure ⟨hx, isPGroup_zpowers_of_isPGroup hR hx⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
