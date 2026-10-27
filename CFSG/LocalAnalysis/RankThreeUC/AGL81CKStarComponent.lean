module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOneIGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem isComponent_kStar_of_isQuasisimple (h : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M) (hq : CFSG.IsQuasisimple ↥(kStar p M H)) :
    CFSG.IsComponent (kStar p M H) ∧ ¬ kStar p M H ≤ starImg p H M := by
  let S : Set (Subgroup (StarGroup p H)) :=
    {C | CFSG.IsComponent C ∧ ¬ C ≤ starImg p H M}
  have hK : kStar p M H = sSup S := h.kStar_eq_sSup_of_not_le hL
  have hne : kStar p M H ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (kStar p M H)).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hq)
  have hSne : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    exact hne (by rw [hK, hS, sSup_empty])
  obtain ⟨C, hCS⟩ := hSne
  have hCcomp : CFSG.IsComponent C := hCS.1
  have hCle : C ≤ kStar p M H := by
    rw [hK]
    exact le_sSup hCS
  have hnorm : kStar p M H ≤ Subgroup.normalizer (C : Set (StarGroup p H)) := by
    rw [hK]
    refine sSup_le fun D hDS => ?_
    by_cases hDC : D = C
    · subst hDC
      exact Subgroup.le_normalizer
    · have hcomm : ⁅D, C⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hDS.1 hCS.1).resolve_left hDC
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer (C : Set (StarGroup p H)))
  haveI hCnorm : (C.subgroupOf (kStar p M H)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hCK : C = kStar p M H := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hCnorm with htop | hcen
    · rw [← Subgroup.map_subgroupOf_eq_of_le hCle, htop, Subgroup.map_top,
        Subgroup.range_subtype]
    · exfalso
      have hab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
        intro x hx y hy
        have hxK : (⟨x, hCle hx⟩ : ↥(kStar p M H)) ∈ C.subgroupOf (kStar p M H) :=
          Subgroup.mem_subgroupOf.mpr hx
        have hcomm := Subgroup.mem_center_iff.mp (hcen hxK) ⟨y, hCle hy⟩
        exact (congrArg Subtype.val hcomm).symm
      have hbot : ⁅C, C⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hab x hx y hy).symm
      have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hCcomp.1.1
      rw [hbot] at hperf
      have hnt : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hCcomp.1
      exact (Subgroup.nontrivial_iff_ne_bot C).mp hnt hperf.symm
  exact ⟨hCK ▸ hCcomp, hCK ▸ hCS.2⟩

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
