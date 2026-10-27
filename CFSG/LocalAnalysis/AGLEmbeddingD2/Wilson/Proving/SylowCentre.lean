module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem inf_centralizer_eq_center_map {X : Type*} [Group X] (H : Subgroup X) :
    H ⊓ Subgroup.centralizer (H : Set X) = (Subgroup.center H).map H.subtype := by
  ext x
  constructor
  · rintro ⟨hxH, hc⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hc (g : X) g.2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)

theorem card_inf_centralizer_eq_card_center {X : Type*} [Group X] (H : Subgroup X) :
    Nat.card (H ⊓ Subgroup.centralizer (H : Set X) : Subgroup X) = Nat.card (Subgroup.center H) := by
  rw [inf_centralizer_eq_center_map H]
  exact Subgroup.card_map_of_injective H.subtype_injective

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
