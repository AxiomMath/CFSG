module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ15
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ21

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Core

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem core_levi {n : ℕ} (hK : Nat.card K = 3 ^ n) {J : Set (Fin Tag.D4.rank)}
    (hJ : J = ({2} : Set (Fin Tag.D4.rank)) ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K} {Γ₁ Γ₂ c₁ c₂ : ModGL Tag.D4 K}
    {a₁ a₂ : Fin Tag.D4.rank → Kˣ} (G : A4Grp J φ Γ₁ Γ₂)
    (hc₁ : c₁ ∈ parabolicSubgroup Tag.D4 K J) (hc₂ : c₂ ∈ parabolicSubgroup Tag.D4 K J)
    (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁) (hΓ₂ : Γ₂ = c₂ * rootDiagUnit Tag.D4 a₂)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x)
    {A : Subgroup (ModGL Tag.D4 K)} (hA : A ≤ parabolicRadical Tag.D4 K J)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA₁ : ∀ a ∈ A, Γ₁ * a * Γ₁⁻¹ = a) (hA₂ : ∀ a ∈ A, Γ₂ * a * Γ₂⁻¹ = a)
    (hbig : 3 ^ (4 * n) ≤ 3 * Nat.card A) : False := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    have := Finite.one_lt_card (α := K)
    rw [hK] at this
    simp at this
  rcases hJ with rfl | rfl
  · have h := J2_card_A hK2 G hc₁ hc₂ hΓ₁ hΓ₂ hne₁ hA hA₁ hA₂
    rw [hK] at h
    have h1 : 3 ^ (4 * n) ≤ 3 ^ (2 * n + 1) := by
      calc 3 ^ (4 * n) ≤ 3 * Nat.card A := hbig
        _ ≤ 3 * (3 ^ n) ^ 2 := Nat.mul_le_mul_left _ h
        _ = 3 ^ (2 * n + 1) := by ring
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    omega
  · by_cases hn1 : n = 1
    · subst hn1
      have h27 : 27 ≤ Nat.card A := by
        have : (3 : ℕ) ^ (4 * 1) = 81 := by norm_num
        omega
      exact J013_n1 (by simpa using hK) hK2 G hc₁ hΓ₁ hne₁ hA hAc hA₁ hA₂ h27
    · have h := J013_card_A hK2 G hc₁ hΓ₁ hne₁ hA hA₁ hA₂
      rw [hK] at h
      have h1 : 3 ^ (4 * n) ≤ 3 ^ (3 * n + 1) := by
        calc 3 ^ (4 * n) ≤ 3 * Nat.card A := hbig
          _ ≤ 3 * (3 ^ n) ^ 3 := Nat.mul_le_mul_left _ h
          _ = 3 ^ (3 * n + 1) := by ring
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
      omega

end Core

end CFSG.LocalAnalysis.GLTheoremA
