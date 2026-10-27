module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2LongRoot
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open EvenCatalog

theorem even_G2_odd_core_including_field_two (K : Type) [Field K] [Finite K]
    (hK : ringChar K = 2) : CFSG.oddCore (adjointGroup .G2 K) = ⊥ := by
  obtain ⟨hDC, -, hperf, hxD, hx2⟩ := G2_long_root_subgroup_perfect K
  set C := adjointGroup .G2 K
  set D := g2LongRootGroup K
  have hDperf : commutator D = ⊤ := by
    have : Group.IsPerfect D := Subgroup.isPerfect_iff.2 hperf
    exact Group.IsPerfect.commutator_eq_top
  set z : C := ⟨pinnedX .G2 K ![1, 0] 1, hDC hxD⟩
  have hz2 : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hx2 hK
  by_contra hne
  set R := CFSG.oddCore C
  have hnc : ¬ R ≤ Subgroup.center C := by
    rw [center_adjointGroup_eq_bot, le_bot_iff]
    exact hne
  have hsolv := (noncentral_normal_solvable_quotient .G2 K R hnc).2.1
  have hzR : z ∈ R := by
    have h := map_eq_one_of_commutator_eq_top hDperf
      ((QuotientGroup.mk' R).comp (Subgroup.inclusion hDC)) ⟨_, hxD⟩
    rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact not_mem_oddCore_of_orderOf_eq_two hz2 hzR

end CFSG.ComponentClassification.UnbalancedCatalog
