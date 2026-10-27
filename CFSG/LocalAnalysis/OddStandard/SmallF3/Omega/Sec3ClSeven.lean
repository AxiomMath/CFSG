module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClShape
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutSeven
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAutStd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IFaith

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadOdd nondegenerate_quadOdd)

theorem cl_closureFix_omegaProj_seven :
    ClosureFix ↥(omegaProj (nondegenerate_quadOdd 3 (ZMod 3))) := by
  have hQ₀ : (quadOdd 3 (ZMod 3)).Nondegenerate := nondegenerate_quadOdd 3 (ZMod 3)
  have h7 : Module.finrank (ZMod 3) (Fin 3 ⊕ Fin 3 ⊕ Unit → ZMod 3) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  have hσ : quadSign (quadOdd 3 (ZMod 3)) = 1 := quadSign_quadOdd 3
  have hπ : piOrth (quadOdd 3 (ZMod 3)) ∉ omegaGroup hQ₀ :=
    piOrth_not_mem_omegaGroup_seven hQ₀ h7
  have hfs : IsFStarGroup (omegaGroup hQ₀) := cl_isFStarGroup_omegaGroup_seven hQ₀ h7
  have hqΩ : CFSG.IsQuasisimple (omegaGroup hQ₀) := isQuasisimple_omegaGroup_seven hQ₀ h7
  let e : omegaGroup hQ₀ ≃* omegaProj hQ₀ :=
    MulEquiv.ofBijective (omegaToProj hQ₀)
      ⟨by
        rw [injective_iff_map_eq_one]
        intro g hg
        rcases (omegaToProj_eq_one_iff hQ₀ g).mp hg with h | h
        · exact Subtype.ext h
        · exact absurd (h ▸ g.2) hπ,
       omegaToProj_surjective hQ₀⟩
  have hq : CFSG.IsQuasisimple ↥(omegaProj hQ₀) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqΩ
  have hF : IsFStarGroup ↥(omegaProj hQ₀) := isFStarGroup_of_mulEquiv e hfs
  haveI : Finite ↥(omegaProj hQ₀) :=
    Finite.of_surjective (omegaToProj hQ₀) (omegaToProj_surjective hQ₀)
  refine closureFix_of_ne_one hq hF ?_
  intro α hα hα1 J hJ
  obtain ⟨A, hA⟩ := sec4I_exists_conj_of_mulAut_std α
  have hαeq : α = projAut hQ₀ A := by
    ext p
    rw [coe_projAut]
    exact hA p
  have hαA : projAut hQ₀ A * projAut hQ₀ A = 1 := by
    rw [← hαeq]
    exact hα
  have hsq : toProj (quadOdd 3 (ZMod 3)) A * toProj (quadOdd 3 (ZMod 3)) A = 1 := by
    apply conjNormal_injective_seven hQ₀ h7 hσ
    rw [map_mul, map_one]
    simpa [projAut] using hαA
  have hAAmem : A * A ∈ piGroup (quadOdd 3 (ZMod 3)) :=
    (QuotientGroup.eq_one_iff (A * A)).mp (by
      show toProj (quadOdd 3 (ZMod 3)) (A * A) = 1
      rw [map_mul]
      exact hsq)
  have hAA : A * A = 1 := by
    rcases mem_piGroup_iff.mp hAAmem with h | h
    · exact h
    · exfalso
      have hEven := ((exists_mul_self_eq_piOrth_iff hQ₀).mp ⟨A, h⟩).1
      rw [h7] at hEven
      exact (by norm_num : ¬ Even (7 : ℕ)) hEven
  have hA1 : A ≠ 1 := by
    intro h1
    exact hα1 (by rw [hαeq, h1]; simp [projAut])
  have hπ1 : ((piOrth (quadOdd 3 (ZMod 3)) : OGroup (quadOdd 3 (ZMod 3))) :
      ProjOrth (quadOdd 3 (ZMod 3))) = 1 := toProj_piOrth
  have hAπ : A ≠ piOrth (quadOdd 3 (ZMod 3)) := by
    intro hπ'
    apply hα1
    rw [hαeq, hπ']
    simp [projAut, hπ1]
  have hfix_ne : fixSp A ≠ ⊥ := by
    intro hfix
    apply hAπ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have htop : commSp A = ⊤ := by
      have hc : fixSp A ⊔ commSp A = ⊤ := codisjoint_iff.mp
        (isCompl_fixSp_commSp (Q := quadOdd 3 (ZMod 3)) hAA).2
      rwa [hfix, bot_sup_eq] at hc
    have hv : v ∈ commSp A := by rw [htop]; exact Submodule.mem_top
    rw [mem_commSp_iff hAA] at hv
    rw [coe_piOrth_apply]
    exact hv
  have hcomm_ne : commSp A ≠ ⊥ := fun h => hA1 ((commSp_eq_bot_iff hAA).mp h)
  have hW : 0 < Module.finrank (ZMod 3) (fixSp A) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hfix_ne (Submodule.finrank_eq_zero.mp h0)
  have hU : 0 < Module.finrank (ZMod 3) (commSp A) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hcomm_ne (Submodule.finrank_eq_zero.mp h0)
  rw [hαeq] at hJ
  exact cl_inFStar_of_isComponentIn_fix hQ₀ (by omega) hAA hW hU hJ

theorem asc82ClosureAt_seven : Asc82ClosureAt ShapeO7 := by
  have hQ₀ : (quadOdd 3 (ZMod 3)).Nondegenerate := nondegenerate_quadOdd 3 (ZMod 3)
  refine asc82ClosureAt_of_omegaStar (P := ShapeO7) (n := 7) (ε := 1)
    (fun X _ h => isOmegaStar_of_lieModel_odd h) (by norm_num) hQ₀ ?_
    (quadSign_quadOdd 3) cl_closureFix_omegaProj_seven
  rw [Module.finrank_fintype_fun_eq_card]
  decide

end CFSG.OddStandard.SmallF3.Omega
