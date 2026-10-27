module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG

open CFSG.ABGLocalTools

theorem pRank_le_of_isSylowOf_le {X : Type} [Group X] [Finite X] {p : Nat} (hp : p.Prime)
    {Y N₁ S : Subgroup X} (hSY : S ≤ Y) (hSyl : IsSylowOf p S Y) (hSN : S ≤ N₁) :
    CFSG.Open.pRank p Y ≤ CFSG.Open.pRank p N₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, rfl⟩ := hSyl
  have hmap : CFSG.Open.pRank p ((T : Subgroup Y).map Y.subtype) =
      CFSG.Open.pRank p (T : Subgroup Y) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup ((T : Subgroup Y).map Y.subtype),
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (T : Subgroup Y)]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (Subgroup.equivMapOfInjective (T : Subgroup Y) Y.subtype Y.subtype_injective)).symm
  have hTY : CFSG.Open.pRank p ((T : Subgroup Y).map Y.subtype) =
      CFSG.Open.pRank p Y := by
    rw [hmap, (CFSG.SectionRank.pRank_sylow T).1,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y]
  rw [← hTY]
  exact CFSG.SectionRank.pRank_mono hp.one_lt hSN

end CFSG
