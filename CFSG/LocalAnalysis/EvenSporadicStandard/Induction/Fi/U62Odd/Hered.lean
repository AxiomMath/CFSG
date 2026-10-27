module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62Odd.Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62Odd.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62Odd.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.U62Odd

theorem u62OddExclHered_of_milestones (hCIT : CITPart2) : U62OddExclHered := by
  intro Y _ _ hU N' hN hidx hkp P hP hq hU62 hodd hev
  by_cases hcat : CFSG.Blueprint.Catalog ↥N'
  · exact not_hasEvenCover_of_overgroup
      (overgroup_of_catalog hN hidx hcat hP hq hU62 hodd) hev
  · have hNtop : N' = ⊤ :=
      Balance.eq_top_of_index_ne_two hidx fun h2 =>
        hcat (Balance.catalog_of_index_two hN h2 hkp)
    subst hNtop
    haveI : IsSimpleGroup ↥(⊤ : Subgroup Y) := hN.isSimpleGroup
    haveI : IsSimpleGroup Y :=
      (Subgroup.topEquiv.symm : Y ≃* ↥(⊤ : Subgroup Y)).isSimpleGroup
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    have hnonab : ∃ a b : Y, a * b ≠ b * a :=
      ⟨a.1, b.1, fun h => hab (Subtype.ext h)⟩
    exact false_of_simple_not_catalog hCIT hU hnonab hkp hcat hP hq hU62 hodd

end CFSG.EvenSporadicStandard.Induction.Fi.U62Odd
