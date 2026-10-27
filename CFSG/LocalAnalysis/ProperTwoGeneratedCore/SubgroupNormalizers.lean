module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalizerClosure

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem subgroup_normalizer_le_overgroup
    (S : Sylow 2 G) (H : Subgroup G) {k : ℕ} (hk : 0 < k)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) k ≤ H)
    (D : Subgroup G) (hDH : D ≤ H) (hrank : k ≤ pRank 2 D) :
    Subgroup.normalizer (D : Set G) ≤ H := by
  intro g hg
  by_contra hgH
  have hDconj : D ≤ H.conjBy g⁻¹ := by
    have hfixed := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem hg)
    change D ≤ H.map (MulAut.conj g⁻¹).toMonoidHom
    rw [← hfixed]
    exact Subgroup.map_mono hDH
  have hlarge := hrank.trans (pRank_mono 2 (by decide) (le_inf hDH hDconj))
  exact (not_lt_of_ge hlarge)
    (conjugate_intersection_rank_lt S H hk hSH hcore g hgH)

theorem two_generated_core_subgroup_normalizer_le
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (D : Subgroup G) (hDH : D ≤ H) (hrank : 2 ≤ pRank 2 D) :
    Subgroup.normalizer (D : Set G) ≤ H :=
  subgroup_normalizer_le_overgroup S H (by decide) hSH hcore D hDH hrank

theorem two_generated_core_subgroup_centralizer_le
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (D : Subgroup G) (hDH : D ≤ H) (hrank : 2 ≤ pRank 2 D) :
    Subgroup.centralizer (D : Set G) ≤ H :=
  (Subgroup.centralizer_le_normalizer (D : Set G)).trans
    (two_generated_core_subgroup_normalizer_le S H hSH hcore D hDH hrank)

end CFSG.ProperTwoGeneratedCore
