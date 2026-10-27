module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dO
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d6f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_card_L_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    Nat.card ↥(q13L t tau x₁ x₂ rho om) ≤ 24 * Nat.card ↥(q13B t tau x₁ x₂ rho om) := by
  obtain ⟨ℰ, hℰ, hUℰ⟩ := exists_isSylowIn_of_le (q13d_U_le_L h hB) (q13b_isPGroup_U h)
  obtain ⟨hℰL, hℰp, hℰidx⟩ := hℰ
  have hri : ℰ.relIndex (q13L t tau x₁ x₂ rho om) * Nat.card ↥ℰ =
      Nat.card ↥(q13L t tau x₁ x₂ rho om) := by
    have h := Subgroup.relIndex_mul_card (H := ℰ) (K := q13L t tau x₁ x₂ rho om)
    rwa [inf_eq_left.mpr hℰL] at h
  have hdiv : ℰ.relIndex (q13L t tau x₁ x₂ rho om) ∣ Nat.card ↥(q13L t tau x₁ x₂ rho om) :=
    ⟨Nat.card ↥ℰ, hri.symm⟩
  have hri_le : ℰ.relIndex (q13L t tau x₁ x₂ rho om) ≤ 3 := by
    rcases q13d_L_card h hB hII with hL | hL | hL
    · have hd : ℰ.relIndex (q13L t tau x₁ x₂ rho om) ∣ 3 * 2 ^ 11 := by
        rw [← hL]; exact hdiv
      have hcop : Nat.Coprime (ℰ.relIndex (q13L t tau x₁ x₂ rho om)) (2 ^ 11) :=
        Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hℰidx
      exact Nat.le_of_dvd (by norm_num) (hcop.dvd_mul_right.mp hd)
    · have hd : ℰ.relIndex (q13L t tau x₁ x₂ rho om) ∣ 3 * 2 ^ 12 := by
        rw [← hL]; exact hdiv
      have hcop : Nat.Coprime (ℰ.relIndex (q13L t tau x₁ x₂ rho om)) (2 ^ 12) :=
        Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hℰidx
      exact Nat.le_of_dvd (by norm_num) (hcop.dvd_mul_right.mp hd)
    · have hd : ℰ.relIndex (q13L t tau x₁ x₂ rho om) ∣ 3 * 2 ^ 13 := by
        rw [← hL]; exact hdiv
      have hcop : Nat.Coprime (ℰ.relIndex (q13L t tau x₁ x₂ rho om)) (2 ^ 13) :=
        Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hℰidx
      exact Nat.le_of_dvd (by norm_num) (hcop.dvd_mul_right.mp hd)
  have hBcard : Nat.card ↥(ℰ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) ≤
      Nat.card ↥(q13B t tau x₁ x₂ rho om) := by
    apply Subgroup.card_le_of_le
    intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [q13B, Subgroup.mem_inf]
    exact ⟨hℰL hg.1, hg.2⟩
  calc Nat.card ↥(q13L t tau x₁ x₂ rho om)
      = ℰ.relIndex (q13L t tau x₁ x₂ rho om) * Nat.card ↥ℰ := hri.symm
    _ ≤ 3 * Nat.card ↥ℰ := Nat.mul_le_mul_right _ hri_le
    _ ≤ 3 * (8 * Nat.card ↥(ℰ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G))) :=
        Nat.mul_le_mul_left _ (q13d_card_le_cent_N h hB hℰp hUℰ)
    _ = 24 * Nat.card ↥(ℰ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)) := by ring
    _ ≤ 24 * Nat.card ↥(q13B t tau x₁ x₂ rho om) := Nat.mul_le_mul_left _ hBcard

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
