module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCharacters
public import CFSG.CharacterTheory.Wreathed.ConditionalOddFourierCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalFiveFixed CFSG.Wreathed.ConditionalOddFourier

variable {G : Type} [Group G] [Fintype G] {basis : FiniteIrreducibleCharacterBasis G}
  {B : Finset basis.index} {p A Bq Dq : basis.index}

theorem basisCombination_xk_labels (hprincipal : (basis.representation p).character = 1)
    (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) {P Q : Fin 2 → basis.index}
    (hP : ∀ e, P e ∈ B) (hQ : ∀ e, Q e ∈ B) (σ τ₀ κ : ℤ) :
    basisCombination basis B (fun φ => fixedPart p A Bq Dq σ τ₀ κ φ +
      (τ₀ * unitVector (P 0) φ + τ₀ * unitVector (P 1) φ + (-κ) * unitVector (Q 0) φ +
        (-κ) * unitVector (Q 1) φ)) =
      -1 - (σ : ℂ) • (basis.representation A).character -
        (τ₀ : ℂ) • (basis.representation Bq).character +
        (κ : ℂ) • (basis.representation Dq).character +
        (τ₀ : ℂ) • ((basis.representation (P 0)).character +
          (basis.representation (P 1)).character) -
        (κ : ℂ) • ((basis.representation (Q 0)).character +
          (basis.representation (Q 1)).character) := by
  rw [basisCombination_eq_fun]
  funext x
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [sum_cast_fixedPart_mul hp hA hBq hDq]
  have h4 := sum_cast_four_mul (B := B) (hP 0) (hP 1) (hQ 0) (hQ 1) τ₀ τ₀ (-κ) (-κ)
    (fun φ => (basis.representation φ).character x)
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib] at h4
  rw [h4]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
    Pi.one_apply, hprincipal]
  push_cast
  ring


theorem weighted_eq_int {A₁ B₁ D₁ : ℤ} (hA : A₁ ≠ 0) (hB : B₁ ≠ 0) (hD : D₁ ≠ 0)
    {c₀ cA cB cD nA nB nD : ℤ}
    (h : (c₀ : ℂ) + cA * ((nA : ℂ) / A₁) + cB * ((nB : ℂ) / B₁) + cD * ((nD : ℂ) / D₁) = 0) :
    c₀ * A₁ * B₁ * D₁ + cA * nA * B₁ * D₁ + cB * nB * A₁ * D₁ + cD * nD * A₁ * B₁ = 0 := by
  have hA' : (A₁ : ℂ) ≠ 0 := by exact_mod_cast hA
  have hB' : (B₁ : ℂ) ≠ 0 := by exact_mod_cast hB
  have hD' : (D₁ : ℂ) ≠ 0 := by exact_mod_cast hD
  have h' : ((c₀ * A₁ * B₁ * D₁ + cA * nA * B₁ * D₁ + cB * nB * A₁ * D₁ +
      cD * nD * A₁ * B₁ : ℤ) : ℂ) = 0 := by
    push_cast
    field_simp at h
    linear_combination h
  exact_mod_cast h'

end CFSG.Wreathed.ConditionalGlobalDegrees
