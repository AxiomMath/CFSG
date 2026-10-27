module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Polynomial Matrix

variable {K : Type*} [Field K]

theorem det_eq_of_pow_eq_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s : Matrix (Fin p) (Fin p) K} {ω : K} (hs : s ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) : s.det = ω := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hirr : Irreducible (X ^ p - C ω : K[X]) := X_pow_sub_C_irreducible_of_prime hp hω
  have hann : aeval s (X ^ p - C ω : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hs]
    simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, Pi.algebraMap_def]
  have hdvd : minpoly K s ∣ (X ^ p - C ω : K[X]) := minpoly.dvd K s hann
  have hmon : (minpoly K s).Monic := minpoly.monic (Matrix.isIntegral s)
  have hnu : ¬ IsUnit (minpoly K s) := minpoly.not_isUnit K s
  obtain ⟨g, hg⟩ := hdvd
  have hgu : IsUnit g := (hirr.isUnit_or_isUnit hg).resolve_left hnu
  have hassoc : Associated (minpoly K s) (X ^ p - C ω) :=
    ⟨hgu.unit, by rw [hg, IsUnit.unit_spec]⟩
  have heq : minpoly K s = X ^ p - C ω :=
    eq_of_monic_of_associated hmon (monic_X_pow_sub_C ω hp.ne_zero) hassoc
  have hdeg : (minpoly K s).natDegree = p := by
    rw [heq, natDegree_X_pow_sub_C]
  have hχ : s.charpoly = minpoly K s := by
    refine eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic s)
      (Matrix.minpoly_dvd_charpoly s) ?_
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hdeg]
  rw [Matrix.det_eq_sign_charpoly_coeff, hχ, heq, Fintype.card_fin,
    (hp.odd_of_ne_two hp2).neg_one_pow, coeff_sub, coeff_X_pow, if_neg hp.ne_zero.symm,
    coeff_C_zero]
  ring

theorem not_pow_of_orderOf [Finite K] {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) {ω : Kˣ}
    (hω : orderOf ω = p ^ a) (hnd : ¬ p ^ (a + 1) ∣ Nat.card K - 1) :
    ∀ b : K, b ^ p ≠ (ω : K) := by
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hb
    exact ω.ne_zero hb.symm
  set u : Kˣ := Units.mk0 b hb0 with hu
  have hup : u ^ p = ω := Units.ext (by simpa [hu] using hb)
  have hk : orderOf u ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard u
  have h1 : orderOf (u ^ p) = orderOf u / Nat.gcd (orderOf u) p := orderOf_pow' u hp.ne_zero
  rw [hup, hω] at h1
  by_cases hpk : p ∣ orderOf u
  · rw [Nat.gcd_eq_right hpk] at h1
    have h2 : orderOf u = p ^ (a + 1) := by
      rw [pow_succ, h1, Nat.div_mul_cancel hpk]
    exact hnd (h2 ▸ hk)
  · have hcop : Nat.gcd (orderOf u) p = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    rw [hcop, Nat.div_one] at h1
    exact hpk (h1 ▸ dvd_pow_self p (by omega))

theorem not_pow_det {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : GL (Fin p) K} {ω : K}
    (hy : (y : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) : ∀ b : K, b ^ p ≠ (y : Matrix (Fin p) (Fin p) K).det := by
  intro b hb
  have hdet0 : (y : Matrix (Fin p) (Fin p) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hb
    exact hdet0 hb.symm
  set s : Matrix (Fin p) (Fin p) K := b⁻¹ • (y : Matrix (Fin p) (Fin p) K) with hsdef
  have hsdet : s.det = 1 := by
    rw [hsdef, Matrix.det_smul, Fintype.card_fin, ← hb, ← mul_pow, inv_mul_cancel₀ hb0, one_pow]
  have hspow : s ^ p = Matrix.scalar (Fin p) (b⁻¹ ^ p * ω) := by
    rw [hsdef, smul_pow, hy]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hω' : ∀ c : K, c ^ p ≠ b⁻¹ ^ p * ω := by
    intro c hc
    apply hω (c * b)
    rw [mul_pow, hc, mul_assoc, mul_comm ω, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hb0,
      one_pow, one_mul]
  have h := det_eq_of_pow_eq_scalar hp hp2 hspow hω'
  rw [hsdet] at h
  apply hω b
  calc b ^ p = b ^ p * 1 := (mul_one _).symm
    _ = b ^ p * (b⁻¹ ^ p * ω) := by rw [← h]
    _ = ω := by rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hb0, one_pow, one_mul]

theorem det_scalar_eq {n : ℕ} (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  have e := congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin n) c)
  rw [Units.val_pow_eq_pow_val, Fintype.card_fin] at e
  exact e

theorem det_conj_eq {n : ℕ} (y g : GL (Fin n) K) :
    ((g⁻¹ * y * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
  have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  calc _ = (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by ring
    _ = _ := by rw [h1, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
