module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
import CFSG.CGT.PushingUpLit.CGT6.EmbLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Quasithin

theorem three_dvd_card_of_three_dvd_card_image {Y A : Type} [Group Y] [Group A] [Finite Y]
    (α : Y →* A) (hα : Function.Surjective α) (hA : 3 ∣ Nat.card A) : 3 ∣ Nat.card Y :=
  hA.trans (Subgroup.card_dvd_of_surjective hα)

theorem three_dvd_card_of_inClassXBlock {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    (hY : InClassXBlock Y) : 3 ∣ Nat.card Y := by
  rcases hY.2 with ⟨n, hn, F, hF, hFin, hcard, α, hα, -⟩ | ⟨n, hn, α, hα, -⟩
  · have hfin : Finite (Matrix.SpecialLinearGroup (Fin 2) F) := Finite.of_surjective α hα
    have h1 : (1 : F) ≠ 0 := one_ne_zero
    let M : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
    have hM3 : M ^ 3 = 1 := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;>
        simp [M, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    have hM1 : M ≠ 1 := by
      intro h
      have := congrArg
        (fun N : Matrix.SpecialLinearGroup (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp [M] at this
    have hord : orderOf M = 3 := orderOf_eq_prime hM3 hM1
    exact three_dvd_card_of_three_dvd_card_image α hα (hord ▸ orderOf_dvd_natCard M)
  · have hm : 3 ≤ 2 * n + 1 := by omega
    let a : Fin (2 * n + 1) := ⟨0, by omega⟩
    let b : Fin (2 * n + 1) := ⟨1, by omega⟩
    let c : Fin (2 * n + 1) := ⟨2, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
    have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
    have h3c := Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
    let g : alternatingGroup (Fin (2 * n + 1)) :=
      ⟨_, h3c.mem_alternatingGroup⟩
    have hord : orderOf g = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact h3c.orderOf
    exact three_dvd_card_of_three_dvd_card_image α hα (hord ▸ orderOf_dvd_natCard g)

theorem kFactBlockFactorThreePrime_of_cgtBlock :
    KFactBlockFactorThreePrime := by
  intro X _ _ hK h3 hC T hT2 hTi
  by_contra hne
  have hKop : CFSG.Open.IsKGroup ↥(⊤ : Subgroup X) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isKGroup_of_subgroup
      (CFSG.CGT.PushingUpLit.CGT6.openIsKGroup_of_isKGroup hK) ⊤
  have hcore : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) = CFSG.pCore 2 X := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore]
  have hchar : CharTwo (⊤ : Subgroup X) := by
    unfold CharTwo
    rw [hcore, top_inf_eq]
    exact hC
  have hsyl : IsSylowTwoOf T (⊤ : Subgroup X) :=
    ⟨le_top, hT2, by
      show ¬ 2 ∣ T.relIndex ⊤
      rwa [Subgroup.relIndex_top_right]⟩
  have hcgs : cgsIn (⊤ : Subgroup X) T ≠ ⊤ := by
    simp only [cgsIn, top_inf_eq]
    exact hne
  obtain ⟨Y, -, -, hY, -⟩ := aschbacherLocalCGTBlock_proved X ⊤ T hKop hchar hsyl hcgs
  exact h3 ((three_dvd_card_of_inClassXBlock hY).trans (Subgroup.card_subgroup_dvd_card Y))

end CFSG.LocalAnalysis.RankThreeTheoremC
