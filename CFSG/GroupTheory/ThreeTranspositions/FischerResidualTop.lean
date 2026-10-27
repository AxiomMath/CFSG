module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual

import CFSG.GroupTheory.ThreeTranspositions.FischerResidualAction

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X]

theorem threeResidualQuot_eq_top_of_isSimpleGroup {E : Set X} (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X)
    {d : X} (hd : d ∈ E) (hs : IsSimpleGroup ↥(threeResidualQuot d)) :
    threeResidualQuot d = ⊤ := by
  obtain ⟨N, hNn, hcent, hNle⟩ := exists_normal_le_threeResidualQuot hP h2 h3 hd
  have hNW : (N.subgroupOf (threeResidualQuot d)).Normal := hNn.subgroupOf _
  rcases hs.eq_bot_or_eq_top_of_normal (N.subgroupOf (threeResidualQuot d)) with hb | ht
  · have hN : N = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hNle
    have htop : (⊤ : Subgroup (X ⧸ Subgroup.center X)) = ⊥ := by
      rw [← hcent, hN]
      exact (Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)).symm
    rw [eq_top_iff, htop]
    exact bot_le
  · have hWN : threeResidualQuot d ≤ N := Subgroup.subgroupOf_eq_top.mp ht
    obtain ⟨e, he⟩ := hP.2.1
    have hdN : (QuotientGroup.mk d : X ⧸ Subgroup.center X) ∈ N :=
      hWN ⟨d, Subgroup.mem_sup_right (Subgroup.mem_zpowers d), rfl⟩
    have hEN : E ⊆ N.comap (QuotientGroup.mk' (Subgroup.center X)) := by
      intro x hx
      have hde : d ∈ {x | IsConj e x} := he ▸ hd
      have hxe : x ∈ {x | IsConj e x} := he ▸ hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp ((IsConj.symm hde).trans hxe)
      have hc := hNn.conj_mem _ hdN (QuotientGroup.mk c : X ⧸ Subgroup.center X)
      simpa using hc
    have hcl : (⊤ : Subgroup X) ≤ N.comap (QuotientGroup.mk' (Subgroup.center X)) := by
      rw [← hP.2.2.2.2]
      exact (Subgroup.closure_le _).mpr hEN
    refine eq_top_iff.mpr fun y _ => hNle ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact hcl (Subgroup.mem_top x)

end CFSG.GroupTheory.ThreeTranspositions
