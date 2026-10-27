module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaR
public import CFSG.CGT.PushingUpLit.BHS7.OmegaFrattini

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem exists_omega_ge (h : MinCex G T) {E₀ : Subgroup Γ}
    (hE₀ : E₀ ∈ omegaSet G T) {F : Subgroup Γ} (hF : IsBTBlock G T F)
    (hFn : ¬ F ≤ cStarIn G T) : ∃ E ∈ omegaSet G T, F ≤ E := by
  by_contra hall
  push Not at hall
  apply hFn
  refine (le_inf hF.le ?_ : F ≤ omegaR G T).trans (omegaR_le_cStarIn h hE₀)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hle : omegaW G T ≤ Subgroup.centralizer ({x} : Set Γ) := by
    refine iSup₂_le fun E hE y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hEG : E ∈ btBlocksG G T := (mem_btBlocksMax_of_mem_bStarG hE.1).1
    rcases six_twelve_c h.charTwo h.sylow hEG hE.2 (mem_btBlocksG_of_isBTBlock hF) with h1 | h1
    · exact absurd h1 (hall E hE)
    · have h2 : ⁅x, y⁆ ∈ (⁅F, E⁆ : Subgroup Γ) :=
        Subgroup.commutator_mem_commutator hx (blockW_le E hy)
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem localCStarConcl_of_omega (h : MinCex G T) {E₀ : Subgroup Γ}
    (hE₀ : E₀ ∈ omegaSet G T) (he : OmegaCStar G T) : LocalCStarConcl G T := by
  refine ⟨omegaSet G T, fun E hE => omega_isBTBlock h hE,
    fun E hE g hg => conjSub_mem_omegaSet hE hg,
    fun E hE E' hE' hne => omega_commute h hE hE' hne, ?_,
    fun F hF hFn => exists_omega_ge h hE₀ hF hFn, he⟩
  exact le_antisymm (sup_le (cStarIn_le G T) omegaJoin_le)
    (le_cStarIn_sup_omegaJoin h (omegaR_le_cStarIn h hE₀))

theorem seven_four_of_omegaCStar (h : MinCex G T) (he : OmegaCStar G T) :
    Seven4 G T := fun E hE hsub =>
  h.not_concl (localCStarConcl_of_omega h (E₀ := E) ⟨hE, hsub⟩ he)

end CFSG.CGT.PushingUpLit.BHS7
