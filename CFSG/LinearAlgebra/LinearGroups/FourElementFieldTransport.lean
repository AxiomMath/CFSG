module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.LinearGroups

open CFSG.Fischer

theorem F4_ω_ne_zero : F4.ω ≠ 0 := by decide

theorem F4_ω_ne_one : F4.ω ≠ 1 := by decide

theorem F4_ω_sq : F4.ω ^ 2 + F4.ω + 1 = 0 := by decide

@[expose] noncomputable def frobeniusF4 : F4 ≃+* F4 :=
  RingEquiv.ofBijective (frobenius F4 2)
    ⟨(frobenius F4 2).injective, Finite.surjective_of_injective (frobenius F4 2).injective⟩

theorem frobeniusF4_apply (x : F4) : frobeniusF4 x = x ^ 2 :=
  frobenius_def 2 x

theorem four_element_field_transport {K : Type*} [Field K] (hK : Nat.card K = 4) {ω : K}
    (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    ∃ φ : F4 ≃+* K, φ F4.ω = ω ∧
      (∀ x : F4, φ (x ^ 2) = φ x ^ 2) ∧
      (∀ x : F4, φ (x + x ^ 2) = φ x + φ x ^ 2) ∧
      (∀ x : F4, φ (x * x ^ 2) = φ x * φ x ^ 2) ∧
      (∀ (m n : Type) (A B : Matrix m n F4), (A + B).map φ = A.map φ + B.map φ) ∧
      (∀ (m n o : Type) [Fintype n] (A : Matrix m n F4) (B : Matrix n o F4),
        (A * B).map φ = A.map φ * B.map φ) ∧
      (∀ (m n : Type) (A : Matrix m n F4),
        ((A.map (· ^ 2)).transpose).map φ = ((A.map φ).map (· ^ 2)).transpose) ∧
      (∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n F4), φ A.det = (A.map φ).det) ∧
      (∀ (n : ℕ) (x y : Fin n → F4), φ (∑ i, x i ^ 2 * y i) = ∑ i, φ (x i) ^ 2 * φ (y i)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  let ψ : F4 ≃+* K := FiniteField.ringEquivOfCardEq (K := F4) (K' := K) (by rw [F4.card, hcard])
  have : CharP K 2 := charP_of_injective_ringHom (f := (ψ : F4 →+* K)) ψ.injective 2
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h3 : ω ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one ω hω0
      rwa [hcard] at this
    have hprod : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hω1)
  have hc2 : ψ F4.ω ^ 2 + ψ F4.ω + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ψ, ← map_add, F4_ω_sq, map_zero]
  have hcases : ψ F4.ω = ω ∨ ψ F4.ω = ω + 1 := by
    have hprod : (ψ F4.ω - ω) * (ψ F4.ω - (ω + 1)) = 0 := by
      linear_combination hc2 + hω2 - (ψ F4.ω * ω + ψ F4.ω + 1) * h2
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have key : ∃ φ : F4 ≃+* K, φ F4.ω = ω := by
    rcases hcases with h | h
    · exact ⟨ψ, h⟩
    · refine ⟨frobeniusF4.trans ψ, ?_⟩
      rw [RingEquiv.trans_apply, frobeniusF4_apply, map_pow, h]
      linear_combination hω2
  obtain ⟨φ, hφ⟩ := key
  refine ⟨φ, hφ, fun x => map_pow φ x 2, fun x => by rw [map_add, map_pow],
    fun x => by rw [map_mul, map_pow], fun m n A B => Matrix.map_add _ (map_add φ) A B,
    fun m n o _ A B => Matrix.map_mul, fun m n A => ?_,
    fun n _ _ A => RingHom.map_det φ.toRingHom A,
    fun n x y => by simp only [map_sum, map_mul, map_pow]⟩
  ext i j
  simp [Matrix.transpose_apply, Matrix.map_apply, map_pow]

end CFSG.LinearGroups
