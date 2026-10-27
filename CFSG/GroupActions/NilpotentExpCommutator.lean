module

public import CFSG.LieType.Steinberg.Adjoint.Exp
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Matrix.Basic

public noncomputable section

namespace CFSG.GroupActions

open scoped Nat

variable {K A : Type*} [CommRing K] [Algebra ℚ K] [Ring A] [Algebra K A]

@[expose] def truncExp (d : ℕ) (M : A) (z : K) : A :=
  ∑ k ∈ Finset.range d, ((k ! : ℚ)⁻¹ • z ^ k) • M ^ k

theorem truncExp_eq_exp [Algebra ℚ A] [IsScalarTower ℚ K A] {d : ℕ} {M : A} (hM : M ^ d = 0)
    (z : K) : truncExp d M z = IsNilpotent.exp (z • M) := by
  rw [IsNilpotent.exp_eq_sum (k := d) (by rw [smul_pow, hM, smul_zero]), truncExp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, smul_assoc]

theorem truncExp_smul (d : ℕ) (M : A) (r z : K) : truncExp d (r • M) z = truncExp d M (r * z) := by
  simp only [truncExp, smul_pow, smul_smul, mul_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, mul_comm (z ^ k)]

theorem truncExp_conj (d : ℕ) (u : Aˣ) (M : A) (z : K) :
    truncExp d ((u : A) * M * ((u⁻¹ : Aˣ) : A)) z =
      (u : A) * truncExp d M z * ((u⁻¹ : Aˣ) : A) := by
  simp only [truncExp, Units.conj_pow, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]

theorem truncExp_commutator {d : ℕ} {a b : A} (ha : a ^ d = 0) (hb : b ^ d = 0)
    (hc : (a * b - b * a) ^ d = 0) (hac : Commute a (a * b - b * a))
    (hbc : Commute b (a * b - b * a)) (s t : K) :
    truncExp d a s * truncExp d b t * truncExp d a (-s) * truncExp d b (-t) =
      truncExp d (a * b - b * a) (s * t) := by
  let _ : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ K)
  have _ : IsScalarTower ℚ K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn : ∀ {x : A}, x ^ d = 0 → ∀ r : K, IsNilpotent (r • x) := fun hx r =>
    ⟨d, by rw [smul_pow, hx, smul_zero]⟩
  have hz : s • a * (t • b) - t • b * (s • a) = (s * t) • (a * b - b * a) := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm t s, ← smul_sub]
  have hu : s • a * ((s * t) • (a * b - b * a)) - (s * t) • (a * b - b * a) * (s • a) = 0 := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hac.eq, mul_comm s (s * t), sub_self]
  rw [truncExp_eq_exp ha, truncExp_eq_exp hb, truncExp_eq_exp ha, truncExp_eq_exp hb,
    truncExp_eq_exp hc, neg_smul, neg_smul,
    CFSG.LieType.Steinberg.Adjoint.commutator_exp' (hn ha s) (hn hb t) (hn hc (s * t))
      IsNilpotent.zero hz hu ((hbc.smul_left t).smul_right (s * t)) (Commute.zero_right _)
      (Commute.zero_right _) (Commute.zero_right _), smul_zero, IsNilpotent.exp_zero, mul_one]

open MvPolynomial in
theorem nilpotent_exponential_commutator {n d : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA : A ^ d = 0) (hB : B ^ d = 0) (hC : (A * B - B * A) ^ d = 0)
    (hAC : A * (A * B - B * A) = (A * B - B * A) * A)
    (hBC : B * (A * B - B * A) = (A * B - B * A) * B) :
    truncExp d (A.map (C : ℚ →+* MvPolynomial (Fin 2) ℚ)) (X 0 : MvPolynomial (Fin 2) ℚ) *
        truncExp d (B.map (C : ℚ →+* MvPolynomial (Fin 2) ℚ)) (X 1 : MvPolynomial (Fin 2) ℚ) *
        truncExp d (A.map (C : ℚ →+* MvPolynomial (Fin 2) ℚ)) (-X 0 : MvPolynomial (Fin 2) ℚ) *
        truncExp d (B.map (C : ℚ →+* MvPolynomial (Fin 2) ℚ)) (-X 1 : MvPolynomial (Fin 2) ℚ) =
      truncExp d ((A * B - B * A).map (C : ℚ →+* MvPolynomial (Fin 2) ℚ))
        (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) := by
  set φ : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) ℚ) :=
    (C : ℚ →+* MvPolynomial (Fin 2) ℚ).mapMatrix
  have hφ : ∀ M, M.map (C : ℚ →+* MvPolynomial (Fin 2) ℚ) = φ M := fun _ => rfl
  have hc : φ A * φ B - φ B * φ A = φ (A * B - B * A) := by
    rw [map_sub, map_mul, map_mul]
  simp only [hφ]
  rw [← hc]
  refine truncExp_commutator (by rw [← map_pow, hA, map_zero]) (by rw [← map_pow, hB, map_zero])
    (by rw [hc, ← map_pow, hC, map_zero]) ?_ ?_ (X 0) (X 1)
  · rw [hc, Commute, SemiconjBy, ← map_mul, ← map_mul, hAC]
  · rw [hc, Commute, SemiconjBy, ← map_mul, ← map_mul, hBC]

end CFSG.GroupActions
