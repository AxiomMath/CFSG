module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj

public section

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalInvolution.Q3.Q3T6
open scoped MatrixGroups

section Lift

set_option synthInstance.maxSize 2000

private theorem s4b_gl3_pow : ∀ g : GL (Fin 2) (ZMod 3),
    g ^ 4 = 1 ∨ g ^ 4 = -1 ∨ g ^ 3 = 1 ∨ g ^ 3 = -1 := by
  decide +kernel

private theorem s4b_gl3_sq : ∀ a b : GL (Fin 2) (ZMod 3), (b * b = a * a ∨ b * b = -(a * a)) →
    ¬ (a * a = 1 ∨ a * a = -1) → (a * b = b * a ∨ a * b = -(b * a)) := by
  decide +kernel

end Lift

theorem conjAut3_eq_one_iff (g : GL (Fin 2) (ZMod 3)) :
    (conjAut g : MulAut SL(2, ZMod 3)) = 1 ↔ g = 1 ∨ g = -1 := by
  rw [← Aut.mem_center_gl3_iff, ← conjAut3_ker, MonoidHom.mem_ker]

theorem conjAut3_eq_iff (g h : GL (Fin 2) (ZMod 3)) :
    (conjAut g : MulAut SL(2, ZMod 3)) = conjAut h ↔ h = g ∨ h = -g := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, conjAut3_eq_one_iff, inv_mul_eq_iff_eq_mul,
    inv_mul_eq_iff_eq_mul, mul_one, mul_neg_one]

theorem aut_sl23_pow (α : MulAut SL(2, ZMod 3)) : α ^ 4 = 1 ∨ α ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := conjAut3_surjective α
  rw [← map_pow, ← map_pow, conjAut3_eq_one_iff, conjAut3_eq_one_iff]
  rcases s4b_gl3_pow g with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem aut_sl23_comm (A B : MulAut SL(2, ZMod 3)) (h : A * A = B * B) (h1 : A * A ≠ 1) :
    A * B = B * A := by
  obtain ⟨a, rfl⟩ := conjAut3_surjective A
  obtain ⟨b, rfl⟩ := conjAut3_surjective B
  rw [← map_mul, ← map_mul, conjAut3_eq_iff] at h
  rw [← map_mul] at h1
  have h1' : ¬ (a * a = 1 ∨ a * a = -1) := fun hh => h1 ((conjAut3_eq_one_iff (a * a)).mpr hh)
  rw [← map_mul, ← map_mul, conjAut3_eq_iff]
  rcases s4b_gl3_sq a b h h1' with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr (by rw [h2, neg_neg])

theorem aut_s4b {A B ζ ξa ξb ξc : MulAut SL(2, ZMod 3)} (hζ : ζ ≠ 1) (hζ2 : ζ * ζ = 1)
    (hAζ : A * ζ = ζ * A) (hBζ : B * ζ = ζ * B) (hA : A * A = ζ * ξa) (hB : B * B = ζ * ξb)
    (hc : A * B * A⁻¹ * B⁻¹ = ζ * ξc) (ha : Odd (orderOf ξa)) (hb : Odd (orderOf ξb))
    (hcc : Odd (orderOf ξc)) : False := by
  have hodd3 : ∀ ξ : MulAut SL(2, ZMod 3), Odd (orderOf ξ) → ξ ^ 3 = 1 := by
    intro ξ hξ
    rcases aut_sl23_pow ξ with h4 | h3
    · have hd : orderOf ξ ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have h1 : orderOf ξ = 1 := by
        have hmem : orderOf ξ ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
        have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [hdiv] at hmem
        obtain ⟨k, hk⟩ := hξ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        omega
      rw [orderOf_eq_one_iff.mp h1, one_pow]
    · exact h3
  have hζ' : ζ ^ 2 = 1 := by rw [pow_two]; exact hζ2
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
  have key : ∀ X ξ : MulAut SL(2, ZMod 3), X * ζ = ζ * X → X * X = ζ * ξ → ξ ^ 3 = 1 →
      X * X = ζ := by
    intro X ξ hXζ hX hξ
    have hξeq : ξ = ζ * (X * X) := by rw [hX, ← mul_assoc, hζ2, one_mul]
    have hXζ' : Commute X ζ := hXζ
    have hcm : Commute ζ (X ^ 2) := hXζ'.symm.pow_right 2
    have h3 : ζ * X ^ 6 = 1 := by
      have e1 : (ζ * X ^ 2) ^ 3 = ζ ^ 3 * (X ^ 2) ^ 3 := Commute.mul_pow hcm 3
      have e2 : ζ ^ 3 = ζ := by rw [pow_succ, hζ', one_mul]
      have e3 : (X ^ 2) ^ 3 = X ^ 6 := by rw [← pow_mul]
      rw [hξeq, ← pow_two X, e1, e2, e3] at hξ
      exact hξ
    have h6 : X ^ 6 = ζ := by
      have := eq_inv_of_mul_eq_one_right h3
      rw [this, hζinv]
    rcases aut_sl23_pow X with h4 | h3'
    · have : X ^ 6 = X * X := by
        rw [show (6 : ℕ) = 4 + 2 by norm_num, pow_add, h4, one_mul, pow_two]
      rw [← this]
      exact h6
    · exfalso
      apply hζ
      rw [← h6, show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3', one_pow]
  have hAA : A * A = ζ := key A ξa hAζ hA (hodd3 ξa ha)
  have hBB : B * B = ζ := key B ξb hBζ hB (hodd3 ξb hb)
  have hAB : A * B = B * A := aut_sl23_comm A B (hAA.trans hBB.symm) (by rw [hAA]; exact hζ)
  have hc1 : A * B * A⁻¹ * B⁻¹ = 1 := by
    rw [hAB]
    group
  have hξc : ξc = ζ := by
    have h2 : ζ * ξc = 1 := by rw [← hc, hc1]
    calc ξc = ζ⁻¹ * (ζ * ξc) := by group
      _ = ζ := by rw [h2, mul_one, hζinv]
  rw [hξc, orderOf_eq_prime hζ' hζ] at hcc
  exact absurd hcc (by decide)

end CFSG.ClassicalInvolution.Q3.Q3AM
