module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.ProjectiveLinear
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Foote.ModuleExclusions CFSG.HardMathSupport.Timmesfeld.Tables

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_inner_or_conj_fieldAut_psl (hn : 3 ≤ n) (hq : 3 ∣ Nat.card K - 1)
    {A : Subgroup (MulAut (projectiveSL n K))} (hA : ∀ α ∈ A, α ^ 3 = 1) (hA9 : Nat.card A = 9) :
    (∃ α ∈ A, α ≠ 1 ∧ α ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) ∨
      (9 ∣ Nat.gcd n (Nat.card K - 1) ∧ ∃ α ∈ A, ∃ (σ : K ≃+* K) (B : GL (Fin n) K),
        orderOf σ = 3 ∧ α = conjAut n K B * fieldAut n K σ * (conjAut n K B)⁻¹) := by
  by_cases hinn : ∃ α ∈ A, α ≠ 1 ∧
      α ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
  · exact Or.inl hinn
  refine Or.inr ?_
  have hA9' : Nat.card A = 3 ^ 2 := by rw [hA9]; norm_num
  have hAe : CFSG.Open.IsElemAbelian 3 A :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hA9', hA⟩
  have h9 : 9 ∣ Nat.gcd n (Nat.card K - 1) := by
    by_contra h9
    obtain ⟨x, ⟨hxA, hxI⟩, hx1⟩ := T1b.meets_inner_projectiveSL hn Nat.prime_three (by norm_num)
      hq (by norm_num [h9]) A hAe hA9'
    exact hinn ⟨x, hxA, hx1, hxI⟩
  have hAD : ¬ A ≤ linearAutGroup n K := fun h => by
    have h1 := T1b.card_le_mul_card_inf_inner_of_le hn Nat.prime_three A hAe h
    have hbot : A ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxA, hxI⟩
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hinn ⟨x, hxA, hx1, hxI⟩
    rw [hbot, Subgroup.card_bot, hA9] at h1
    omega
  obtain ⟨α, hαA, hαD⟩ := SetLike.not_le_iff_exists.1 hAD
  obtain ⟨M, σ, hαM, hσ3⟩ := exists_semilinear_of_cube_eq_one hn (hA α hαA)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hαD (mem_linearAutGroup_iff.mpr ⟨M, by rw [hαM, map_one, mul_one]⟩)
  obtain ⟨hσord, B, hαB⟩ := exists_conj_fieldAut_of_cube_eq_one hn (hA α hαA) σ M hαM hσ1 hσ3
  exact ⟨h9, α, hαA, σ, B, hσord, hαB⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
