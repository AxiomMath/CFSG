module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG

theorem solvableRadical_normal (G : Type) [Group G] [Finite G] :
    (solvableRadical G).Normal :=
  ABGLocalTools.solvableRadical_normal (H := G)

theorem isSolvable_solvableRadical (G : Type) [Group G] [Finite G] :
    Group.IsSolvable ↥(solvableRadical G) :=
  ABGLocalTools.solvableRadical_isSolvable (H := G)

theorem solvableRadical_eq_bot_of_isSimpleGroup (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) : solvableRadical G = ⊥ := by
  haveI : (solvableRadical G).Normal := solvableRadical_normal G
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (solvableRadical G) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    haveI : Group.IsSolvable ↥(solvableRadical G) := isSolvable_solvableRadical G
    have hsurj : Function.Surjective (Subgroup.subtype (solvableRadical G)) := by
      have hrange : (Subgroup.subtype (solvableRadical G)).range = ⊤ := by
        rw [Subgroup.range_subtype, h]
      exact MonoidHom.range_eq_top.mp hrange
    have hsolv : Group.IsSolvable G :=
      Group.isSolvable_of_surjective (f := Subgroup.subtype (solvableRadical G)) hsurj
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem oddCore_le_solvableRadical (G : Type) [Group G] [Finite G] :
    CFSG.oddCore G ≤ solvableRadical G :=
  le_sSup ⟨inferInstance, CFSG.FeitThompson.isSolvable_of_odd_natCard _ (ABGLocalTools.odd_card_oddCore (H := G))⟩

end CFSG
