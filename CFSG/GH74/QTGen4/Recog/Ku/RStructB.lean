module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.HSTypeS6

public section

namespace CFSG.GH74.QTGen4.Ku

theorem offdiag_comm_of_fix {F : Type} [Field F] (h2 : (2 : F) = 0) {a b c a' b' c' p q : F}
    (h1 : a * p + b * q = p) (h1' : c * p + a * q = q)
    (h1'' : a' * p + b' * q = p) (h1''' : c' * p + a' * q = q)
    (hne : p ≠ 0 ∨ q ≠ 0) : b * c' = b' * c := by
  have e1 : b * q = (a + 1) * p := by linear_combination h1 - a * p * h2
  have e2 : c * p = (a + 1) * q := by linear_combination h1' - a * q * h2
  have e1' : b' * q = (a' + 1) * p := by linear_combination h1'' - a' * p * h2
  have e2' : c' * p = (a' + 1) * q := by linear_combination h1''' - a' * q * h2
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      rcases hne with h | h
      · exact absurd hp h
      · exact h
    have hb : b = 0 := by
      have : b * q = 0 := by rw [e1, hp, mul_zero]
      exact (mul_eq_zero.mp this).resolve_right hq
    have hb' : b' = 0 := by
      have : b' * q = 0 := by rw [e1', hp, mul_zero]
      exact (mul_eq_zero.mp this).resolve_right hq
    rw [hb, hb']; ring
  by_cases hq : q = 0
  · have hc : c = 0 := by
      have : c * p = 0 := by rw [e2, hq, mul_zero]
      exact (mul_eq_zero.mp this).resolve_right hp
    have hc' : c' = 0 := by
      have : c' * p = 0 := by rw [e2', hq, mul_zero]
      exact (mul_eq_zero.mp this).resolve_right hp
    rw [hc, hc']; ring
  have key : (b * c' - b' * c) * (p * q) = 0 := by
    linear_combination (c' * p) * e1 + (a + 1) * p * e2' - (c * p) * e1' - (a' + 1) * p * e2
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hpq)

theorem fix_span {F : Type} [Field F] (h2 : (2 : F) = 0) {a b c d p q v₁ v₂ : F}
    (hdet : a * d - b * c = 1) (h1 : a * p + b * q = p) (h1' : c * p + d * q = q)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    ∃ t : F, (a - 1) * v₁ + b * v₂ = t * p ∧ c * v₁ + (d - 1) * v₂ = t * q := by
  have hX : (a - 1) * (d - 1) - b * c = 0 := by
    have hdp : ((a - 1) * (d - 1) - b * c) * p = 0 := by
      linear_combination (d - 1) * h1 - b * h1'
    have hdq : ((a - 1) * (d - 1) - b * c) * q = 0 := by
      linear_combination (a - 1) * h1' - c * h1
    rcases hne with hp | hq
    · exact (mul_eq_zero.mp hdp).resolve_right hp
    · exact (mul_eq_zero.mp hdq).resolve_right hq
  have htr : a + d = 0 := by linear_combination (-1 : F) * hX + hdet + h2
  have e1 : b * q = (a + 1) * p := by linear_combination h1 - a * p * h2
  have e2 : c * p = (a + 1) * q := by linear_combination h1' - q * htr
  have hcross : ((a - 1) * v₁ + b * v₂) * q = (c * v₁ + (d - 1) * v₂) * p := by
    linear_combination v₂ * e1 - v₁ * e2 + (p * v₂ - q * v₁ - d * p * v₂) * h2 + p * v₂ * htr
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      rcases hne with h | h
      · exact absurd hp h
      · exact h
    refine ⟨(c * v₁ + (d - 1) * v₂) / q, ?_, ?_⟩
    · rw [hp, mul_zero]
      have h0 : ((a - 1) * v₁ + b * v₂) * q = 0 := by rw [hcross, hp, mul_zero]
      exact (mul_eq_zero.mp h0).resolve_right hq
    · rw [div_mul_cancel₀ _ hq]
  · refine ⟨((a - 1) * v₁ + b * v₂) / p, ?_, ?_⟩
    · exact (div_mul_cancel₀ _ hp).symm
    · rw [div_mul_eq_mul_div, eq_div_iff hp]
      exact hcross.symm

end CFSG.GH74.QTGen4.Ku
