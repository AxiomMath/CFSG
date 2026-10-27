module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
public import CFSG.GH74.BNPair.Defs

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.GH74.BNPair Subgroup

@[expose] def GomiAtomsOnlyTop (X : Type) [Group X] : Prop :=
  ∀ U Q : Subgroup X, IsSylowOf 2 U ⊤ → normalizer (U : Set X) < Q → Q < ⊤ → IsGomiAtom ⊤ U Q

theorem isGomiAtom_of_gomiAtomsOnlyTop {G : Type} [Group G] [Finite G] {L U P : Subgroup G}
    (h : GomiAtomsOnlyTop ↥L) (hU : IsSylowOf 2 U L) (hBP : L ⊓ normalizer (U : Set G) < P)
    (hPL : P < L) : IsGomiAtom L U P := by
  have hUle : U ≤ L := hU.le
  have hPle : P ≤ L := hPL.le
  have hU's : IsSylowOf 2 (U.subgroupOf L) ⊤ := (isSylowOf_top_subgroupOf_iff hUle).2 hU
  have hNP' : normalizer (U.subgroupOf L : Set ↥L) < P.subgroupOf L := by
    apply (Subgroup.map_lt_map_iff_of_injective L.subtype_injective).mp
    rw [← inf_normalizer_eq_map_normalizer_subgroupOf hUle,
      Subgroup.map_subgroupOf_eq_of_le hPle]
    exact hBP
  have hP'top : P.subgroupOf L < ⊤ := by
    apply (Subgroup.map_lt_map_iff_of_injective L.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hPle, ← L.subtype.range_eq_map,
      Subgroup.range_subtype]
    exact hPL
  exact (isGomiAtom_iff_subgroupOf hUle hPle).2
    (h (U.subgroupOf L) (P.subgroupOf L) hU's hNP' hP'top)

end CFSG.GroupTheory
