module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Comb5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma75a_of (h36 : Asc82Lemma36) (hP : Asc82Tab6P) : Asc82Lemma75a := by
  intro G _ _ t L S z hctx
  exact hP.sylow_E16 G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36)

theorem asc82Lemma75b_of (h36 : Asc82Lemma36) (hP : Asc82Tab6P) : Asc82Lemma75b := by
  intro G _ _ t L S z hctx B hB
  obtain ⟨h1, h2, h3⟩ := hP.aut_B G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36) B hB
  refine ⟨h1, h2, h3, ?_⟩
  have hzB : z ∈ B :=
    hP.center_le G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36) B hB hctx.z_mem_centerIn
  have hz1 : z ≠ 1 := by
    intro hz
    have hzord : orderOf z = 1 := orderOf_eq_one_iff.mpr hz
    rw [hctx.pocket.1] at hzord
    norm_num at hzord
  have hN : L ⊓ normalizer (B : Set G) ≤ normalizer (B : Set G) := inf_le_right
  obtain ⟨φ, hφ⟩ := h3
  exact closure_conj_eq_of_permModule hφ hN hzB hz1

end CFSG.OddStandard.SmallF3.Omega
