module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_ge_of_sylow {X C T : Subgroup G} (hTX : T ≤ X) (hT : IsSylowOf 2 T C) :
    ∃ P : Subgroup G, IsSylowOf 2 P X ∧ T ≤ P ∧ P ⊓ C = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf X) := hT.isPGroup.comap_subtype
  obtain ⟨P', hP'⟩ := hTp.exists_le_sylow
  have hPsyl : IsSylowOf 2 ((P' : Subgroup ↥X).map X.subtype) X := ⟨P', rfl⟩
  have hTP : T ≤ (P' : Subgroup ↥X).map X.subtype := fun t ht =>
    ⟨⟨t, hTX ht⟩, hP' (show (⟨t, hTX ht⟩ : ↥X) ∈ T.subgroupOf X from ht), rfl⟩
  refine ⟨_, hPsyl, hTP, ?_⟩
  exact hT.eq_of_le (le_inf hTP hT.le) inf_le_right hPsyl.isPGroup.to_inf_left

end CFSG.EvenSporadicStandard.M22Std
