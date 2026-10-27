module

public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2LongRoot

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

theorem G2_solvable_normal_subgroups_trivial
    (K : Type) [Field K]
    (R : Subgroup (adjointGroup .G2 K)) [R.Normal] (hR : Group.IsSolvable R) : R = ⊥ := by
  by_contra hne
  have hRZ : ¬R ≤ Subgroup.center (adjointGroup .G2 K) := by
    rw [center_adjointGroup_eq_bot_field, le_bot_iff]
    exact hne
  have hquot := (noncentral_normal_solvable_quotient .G2 K R hRZ).2.1
  have hC : Group.IsSolvable (adjointGroup .G2 K) :=
    Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  obtain ⟨hDC, hD1, hDperf, -, -⟩ := G2_long_root_subgroup_perfect K
  set D := g2LongRootGroup K
  have hDsol : Group.IsSolvable D :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDC)
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hDperf
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot _).2 hD1
  exact Group.IsPerfect.not_isSolvable D hDsol

end CFSG.LieType.Chevalley
