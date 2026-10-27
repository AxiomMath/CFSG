module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem field_root_eq (σ : K →+* K) (M : GL ι K) {X Y A B : Matrix ι ι K} {ξ ζ a b : K}
    (hXY : X * Y = ξ • (Y * X)) (hAB : A * B = ζ • (B * A))
    (hX : (M : Matrix ι ι K) * X.map σ * ((M⁻¹ : GL ι K) : Matrix ι ι K) = a • A)
    (hY : (M : Matrix ι ι K) * Y.map σ * ((M⁻¹ : GL ι K) : Matrix ι ι K) = b • B)
    (ha : a ≠ 0) (hb : b ≠ 0) (hBA : B * A ≠ 0) : σ ξ = ζ := by
  set N := (M : Matrix ι ι K)
  set N' := ((M⁻¹ : GL ι K) : Matrix ι ι K)
  have hNN : N' * N = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : ∀ Z W : Matrix ι ι K, N * Z * N' * (N * W * N') = N * (Z * W) * N' := fun Z W => by
    rw [show N * Z * N' * (N * W * N') = N * Z * (N' * N) * W * N' by
      simp only [Matrix.mul_assoc], hNN, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hσ : X.map σ * Y.map σ = σ ξ • (Y.map σ * X.map σ) := by
    rw [← Matrix.map_mul, hXY, Matrix.map_smul' _ _ _ (map_mul σ), Matrix.map_mul]
  have key : (a • A) * (b • B) = σ ξ • ((b • B) * (a • A)) := by
    rw [← hX, ← hY, hc, hc, hσ, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hAB, smul_smul,
    smul_smul, smul_smul, smul_smul] at key
  have h0 := sub_eq_zero.2 key
  rw [← sub_smul] at h0
  rcases smul_eq_zero.1 h0 with h | h
  · have h' : a * b * (ζ - σ ξ) = 0 := by linear_combination h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left (mul_ne_zero ha hb))).symm
  · exact absurd h hBA

theorem val_mul_ne_zero [Nonempty ι] (A B : GL ι K) :
    ((B : Matrix ι ι K) * (A : Matrix ι ι K)) ≠ 0 := by
  intro h0
  have h1 := (Matrix.isUnit_iff_isUnit_det _).1 (B * A).isUnit
  rw [Units.val_mul, h0, det_zero] at h1
  exact not_isUnit_zero h1

theorem val_mul_scalar (A : GL ι K) (u : Kˣ) :
    ((A * GeneralLinearGroup.scalar ι u : GL ι K) : Matrix ι ι K) =
      (u : K) • (A : Matrix ι ι K) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, smul_eq_mul_diagonal]

end Matrix

section Linear

open LinearFlag

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem eq_smul_of_conjAut_eq (hn : 3 ≤ n) {A X' : GL (Fin n) K}
    (h : conjAut n K X' = conjAut n K A) :
    ∃ a : Kˣ, (X' : Matrix (Fin n) (Fin n) K) = (a : K) • (A : Matrix (Fin n) (Fin n) K) := by
  have h1 : conjAut n K (A⁻¹ * X') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨a, ha⟩ := (conjAut_eq_one_iff hn _).1 h1
  refine ⟨a, ?_⟩
  rw [← val_mul_scalar, ← ha, mul_inv_cancel_left]

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} (h : UnitaryFieldData p f K)
  (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem semilinearAutHom_conj_linearSimAut (y : semilinearSimilitudes h r ε)
    (X : linearSimilitudes h r ε) :
    ∃ hmem : (y : SemiGL (HypIndex r ε) K).left * glAut (y : SemiGL (HypIndex r ε) K).right
        (X : GL (HypIndex r ε) K) * (y : SemiGL (HypIndex r ε) K).left⁻¹ ∈
          linearSimilitudes h r ε,
      semilinearAutHom h hr hε y * linearSimAut h hr hε X * (semilinearAutHom h hr hε y)⁻¹ =
        linearSimAut h hr hε ⟨_, hmem⟩ := by
  have hz := semiGL_conj_inl (y : SemiGL (HypIndex r ε) K) (X : GL (HypIndex r ε) K)
  have hmem : (y : SemiGL (HypIndex r ε) K).left * glAut (y : SemiGL (HypIndex r ε) K).right
      (X : GL (HypIndex r ε) K) * (y : SemiGL (HypIndex r ε) K).left⁻¹ ∈
        linearSimilitudes h r ε := by
    change SemidirectProduct.inl _ ∈ semilinearSimilitudes h r ε
    rw [← hz]
    exact (y * linearToSemilinear h X * y⁻¹).2
  refine ⟨hmem, ?_⟩
  rw [linearSimAut, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext hz)

variable (hn : 3 ≤ 2 * r + ε)

include hn in
theorem eq_smul_of_linearSimAut_eq {A X' : linearSimilitudes h r ε}
    (heq : linearSimAut h hr hε X' = linearSimAut h hr hε A) :
    ∃ a : Kˣ, ((X' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (a : K) • ((A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  have h1 : linearSimAut h hr hε (A⁻¹ * X') = 1 := by rw [map_mul, map_inv, heq, inv_mul_cancel]
  obtain ⟨a, ha⟩ := (linearSimAut_eq_one_iff h hr hε hn _).1 h1
  refine ⟨a, ?_⟩
  rw [← val_mul_scalar, ← ha]
  simp

include hn in
theorem unitary_field_root {A B : linearSimilitudes h r ε} {ζ : K}
    (hAB : ((A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (B : GL (HypIndex r ε) K) =
      ζ • (((B : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (A : GL (HypIndex r ε) K)))
    (y : semilinearSimilitudes h r ε)
    (hA : linearSimAut h hr hε A * semilinearAutHom h hr hε y =
      semilinearAutHom h hr hε y * linearSimAut h hr hε A)
    (hB : linearSimAut h hr hε B * semilinearAutHom h hr hε y =
      semilinearAutHom h hr hε y * linearSimAut h hr hε B) :
    (y : SemiGL (HypIndex r ε) K).right ζ = ζ := by
  have : Nonempty (HypIndex r ε) := ⟨Sum.inl ⟨0, hr⟩⟩
  have hBA := val_mul_ne_zero (A : GL (HypIndex r ε) K) (B : GL (HypIndex r ε) K)
  obtain ⟨hmA, h1⟩ := semilinearAutHom_conj_linearSimAut h hr hε y A
  obtain ⟨hmB, h2⟩ := semilinearAutHom_conj_linearSimAut h hr hε y B
  rw [← hA, mul_inv_cancel_right] at h1
  rw [← hB, mul_inv_cancel_right] at h2
  obtain ⟨a, ha⟩ := eq_smul_of_linearSimAut_eq h hr hε hn h1.symm
  obtain ⟨b, hb⟩ := eq_smul_of_linearSimAut_eq h hr hε hn h2.symm
  have h3 := field_root_eq ((y : SemiGL (HypIndex r ε) K).right : K →+* K)
    (y : SemiGL (HypIndex r ε) K).left hAB hAB ha hb a.ne_zero b.ne_zero hBA
  exact h3

end Unitary

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
