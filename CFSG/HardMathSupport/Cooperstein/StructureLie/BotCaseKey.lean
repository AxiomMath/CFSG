module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseNorm
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseKeyForm
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseKeySym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial

theorem keyNormalizer : KeyNormalizer := by
  intro W _ _ _ hn H L hgen hirr hLH hidx hperf hL1 g hg
  have h3 : 3 ≤ finrank (ZMod 2) W := by
    by_contra hlt
    exact hL1 (eq_bot_of_isPerfect_of_finrank_le_two (by omega) L hperf)
  obtain ⟨-, hcases⟩ := shape_of_perfect_index_two hn H L hgen hirr hLH hidx hperf hL1
  have : Finite W := Module.finite_of_finite (ZMod 2)
  rcases hcases with ⟨-, f, hnd, halt, hH⟩ | ⟨Q, hQ, hH⟩ | ⟨he, hsym⟩
  · have hhalt : ∀ v, f v v = 0 := halt
    have hcomm : ∀ u v, f u v = f v u := by
      intro u v
      have h1 := hhalt (u + v)
      simp only [map_add, LinearMap.add_apply, hhalt u, hhalt v] at h1
      generalize f u v = α at h1 ⊢
      generalize f v u = β at h1 ⊢
      revert α β
      decide
    rw [hH] at hg ⊢
    exact mem_bilinIsometryGroup_of_mem_normalizer hhalt hcomm (fun u hu => hnd.1 u hu) hg
  · rw [hH] at hg ⊢
    exact mem_orthGL_of_mem_normalizer Q hQ hg
  · have h4 : 4 ≤ finrank (ZMod 2) W := by
      obtain ⟨k, hk⟩ := he
      omega
    exact mem_of_mem_normalizer_sym h4 H hsym g hg

end CFSG.HardMathSupport.Cooperstein.StructureLie
