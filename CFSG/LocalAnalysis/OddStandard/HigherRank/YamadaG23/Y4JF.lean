module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJNorm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_T_normF (hH : F33Hyp s e) : s.T ≤ normalizer (s.fr.F : Set G) := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting (L := L) hH.hS
  have hFL : s.fr.F ≤ L := y54_F_le_L s
  have hF2 : IsPGroup 2 ↥s.fr.F :=
    s3_isPGroup_of_le s ((s3_F_le_A s).trans (s3_A_le_S s))
  have hF'S : s.fr'.F ≤ s.fr'.S := by
    rw [SFrame.F, SFrame.S, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mul_mem s.fr'.S (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.mul_mem s.fr'.S (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.pow_mem s.fr'.S (Subgroup.subset_closure (by simp)) 2
  have hS'_norm : s.fr'.S ≤ normalizer (s.fr'.F : Set (MulAut (L ⧸ center L))) :=
    (normal_subgroupOf_iff_le_normalizer hF'S).mp
      (s.facts.2.2.2.1.2.2.2.2.1.1.1)
  have hσ'_norm : s.fr'.σ ∈ normalizer (s.fr'.F : Set (MulAut (L ⧸ center L))) :=
    (s.facts.2.2.2.2.2.2.2.2.2).2.1
  have hSσ_norm : s.fr'.Sσ ≤ normalizer (s.fr'.F : Set (MulAut (L ⧸ center L))) := by
    rw [Frame.Sσ]
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS'_norm (Subgroup.subset_closure (by simp))
    · exact hS'_norm (Subgroup.subset_closure (by simp))
    · exact hS'_norm (Subgroup.subset_closure (by simp))
    · exact hS'_norm (Subgroup.subset_closure (by simp))
    · exact hS'_norm (Subgroup.subset_closure (by simp))
    · exact hσ'_norm
  intro x hx
  have hxN : x ∈ normalizer (L : Set G) := s3_T_le_N s hH.hS hx
  let α : MulAut (L ⧸ center L) := jHom L ⟨x, hxN⟩
  have hxα : ActsAs L x α := jHom_actsAs L ⟨x, hxN⟩
  refine (mem_normalizer_iff_jSub (L := L) hH.hZ hFL hF2 hxα).mpr ?_
  rw [s3_jSub_F hH.hS hH.hZ s]
  have hαj : α ∈ jSub L s.T := (mem_jSub L).mpr ⟨x, hx, hxα⟩
  by_cases hRT : s.R = s.T
  · have hαS : α ∈ s.fr'.S := by
      simpa [← hRT, s3_jSub_R (L := L) s] using hαj
    exact hS'_norm hαS
  · exact hSσ_norm (by simpa [s3_jSub_T (L := L) s hH.hS hH.hOut hRT] using hαj)

end CFSG.OddStandard.HigherRank.YamadaG23
