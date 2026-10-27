module

public import CFSG.Timmesfeld.ARS.Induction

public section

namespace CFSG.CGT.T75E

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Blueprint

theorem lieModel_psl_of_isTI {K : Type} [Group K] {R : Set (Subgroup K)} (hars : ARS.Hyp K R)
    {Δ : Set (Subgroup K)} (hΔ : IsTI R Δ) {A : Subgroup K} (hA : A ∈ Δ) :
    ∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ LieModel K .PSL n 2 f := by
  have := hars.finite
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun _ hA _ hB e => eq_of_omegaSet_eq hars hA hB e
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow hars.root hars.noIsolated hars.nondeg hΩ
    hΔ.isWeakTI hA
  obtain ⟨hm2, X, hX⟩ :=
    Linear.exists_isRootFrame hars.root hars.noIsolated hars.nondeg hΩ hΔ hA hm
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨f, hf, -, hL⟩ := hX.isConfig.lieModel_A_two hars.root hars.noIsolated hars.center
      hX.iSup_adj_eq_top
    exact ⟨3, f, le_rfl, hf, hL⟩
  · obtain ⟨f, hf, -, hL⟩ := hX.isConfig.lieModel_A hars.root hars.noIsolated hars.center hm3
      hX.iSup_adj_eq_top
    exact ⟨m + 1, f, by omega, hf, hL⟩

end CFSG.CGT.T75E
