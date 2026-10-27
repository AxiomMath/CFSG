module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField
open CatalogueBHermitian CFSG.LieType.Universal.Unitary

universe u

theorem graphField_inverse_eq_conjugateTranspose (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (A : GL (Fin n) K) :
    glGraphFieldAut n K sigma A⁻¹ = conjugateTransposeGL sigma A := by
  apply Units.ext
  rw [glGraphFieldAut_matrix, inv_inv, conjugateTransposeGL_val]
  rfl

theorem conjugateTransposeGL_mul (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (A B : GL (Fin n) K) :
    conjugateTransposeGL sigma (A * B) =
      conjugateTransposeGL sigma B * conjugateTransposeGL sigma A := by
  apply Units.ext
  exact conjTr_mul sigma A.val B.val

theorem conjugateTransposeGL_scalar (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (c : Kˣ) :
    conjugateTransposeGL sigma (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom c) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp [conjugateTransposeGL, conjTr, GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply]

theorem conjugateTransposeGL_involutive (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (A : GL (Fin n) K) :
    conjugateTransposeGL sigma (conjugateTransposeGL sigma A) = A := by
  apply Units.ext
  exact conjugateTranspose_involutive sigma hsigma A.val

theorem graphField_conjugateTranspose_scalar (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c = A * glGraphFieldAut n K sigma A) :
    conjugateTransposeGL sigma A = GeneralLinearGroup.scalar (Fin n) c⁻¹ * A := by
  have h : A * (conjugateTransposeGL sigma A)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) c := by
    rw [← graphField_inverse_eq_conjugateTranspose, ← map_inv, inv_inv]
    exact hc.symm
  have hA := mul_inv_eq_iff_eq_mul.mp h
  calc
    conjugateTransposeGL sigma A =
        (GeneralLinearGroup.scalar (Fin n) c)⁻¹ *
          (GeneralLinearGroup.scalar (Fin n) c * conjugateTransposeGL sigma A) := by group
    _ = GeneralLinearGroup.scalar (Fin n) c⁻¹ * A := by rw [← hA, map_inv]

theorem graphField_scalar_norm_one (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c = A * glGraphFieldAut n K sigma A) :
    sigma (c : K) * (c : K) = 1 := by
  have hstar := graphField_conjugateTranspose_scalar n K A sigma c hc
  have hdouble := congrArg (conjugateTransposeGL sigma) hstar
  rw [conjugateTransposeGL_involutive n K sigma hsigma,
    conjugateTransposeGL_mul, conjugateTransposeGL_scalar, hstar] at hdouble
  have hcentral := GeneralLinearGroup.scalar_commute
    (Units.map sigma.toMonoidHom c⁻¹) A
  have hscalar : GeneralLinearGroup.scalar (Fin n)
      (c⁻¹ * Units.map sigma.toMonoidHom c⁻¹) = 1 := by
    apply mul_right_cancel (b := A)
    rw [map_mul, mul_assoc, hcentral, ← mul_assoc, one_mul]
    exact hdouble.symm
  let i : Fin n := ⟨0, by omega⟩
  have hentry := congrArg (fun M : GL (Fin n) K => M i i) hscalar
  have hentryUnit : (c⁻¹ * Units.map sigma.toMonoidHom c⁻¹ : Kˣ).val = 1 := by
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply, ite_true] using hentry
  have hinv : (c : K)⁻¹ * (sigma (c : K))⁻¹ = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val] at hentryUnit
    change (c : K)⁻¹ * sigma (c⁻¹ : Kˣ).val = 1 at hentryUnit
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hentryUnit
    exact hentryUnit
  have h := congrArg (fun x : K => x⁻¹) hinv
  simpa only [_root_.mul_inv_rev, inv_inv, inv_one] using h

theorem exists_hermitian_graphField_matrix (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c = A * glGraphFieldAut n K sigma A) :
    ∃ b : Kˣ,
      conjTr sigma (GeneralLinearGroup.scalar (Fin n) b * A).val =
          (GeneralLinearGroup.scalar (Fin n) b * A).val ∧
        graphFieldAction n K (GeneralLinearGroup.scalar (Fin n) b * A) sigma =
          graphFieldAction n K A sigma := by
  have hnorm := graphField_scalar_norm_one n K hn A sigma hsigma c hc
  have hinvnorm : sigma (c⁻¹ : Kˣ) * (c⁻¹ : Kˣ) = 1 := by
    simp only [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hnorm, inv_one]
  obtain ⟨b, hb⟩ := CatalogueBUnitaryNorm.exists_norm_one_ratio sigma hsigma hne c⁻¹ hinvnorm
  have hunit : Units.map sigma.toMonoidHom b * c⁻¹ = b := by
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change sigma (b : K) * (c : K)⁻¹ = (b : K)
    have h := (div_eq_iff ((map_ne_zero sigma).mpr (Units.ne_zero b))).mp hb
    simpa only [mul_comm, Units.val_inv_eq_inv_val] using h.symm
  refine ⟨b, ?_, graphFieldAction_scalar_mul n K b A sigma⟩
  have hstar := graphField_conjugateTranspose_scalar n K A sigma c hc
  have hB : conjugateTransposeGL sigma (GeneralLinearGroup.scalar (Fin n) b * A) =
      GeneralLinearGroup.scalar (Fin n) b * A := by
    rw [conjugateTransposeGL_mul, conjugateTransposeGL_scalar, hstar]
    calc
      _ = GeneralLinearGroup.scalar (Fin n) c⁻¹ *
          GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b) * A := by
        rw [mul_assoc (GeneralLinearGroup.scalar (Fin n) c⁻¹) A
          (GeneralLinearGroup.scalar (Fin n) (Units.map sigma.toMonoidHom b)),
          ← GeneralLinearGroup.scalar_commute (Units.map sigma.toMonoidHom b) A,
          ← mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin n) b * A := by
        rw [← map_mul, mul_comm c⁻¹, hunit]
  exact congrArg Units.val hB

theorem graphField_involution_conjugacy (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hne : sigma ≠ 1) (hsquare : graphFieldAction n K A sigma ^ 2 = 1) :
    sigma ^ 2 = 1 ∧ ∃ H : GL (Fin n) K,
      graphFieldAction n K A sigma = innerDiagonalAction n K H *
        pslGraphFieldAut n K sigma * (innerDiagonalAction n K H)⁻¹ := by
  obtain ⟨hsigma, c, hc⟩ := graphField_involution_scalar n K hn A sigma hsquare
  obtain ⟨b, hhermitian, haction⟩ :=
    exists_hermitian_graphField_matrix n K (by omega) A sigma hsigma hne c hc
  let B := GeneralLinearGroup.scalar (Fin n) b * A
  obtain ⟨H, hH⟩ := exists_hermitian_factorization sigma hsigma hne B hhermitian
  have hB : B = H * glGraphFieldAut n K sigma H⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, graphField_inverse_eq_conjugateTranspose]
    exact hH
  refine ⟨hsigma, H, ?_⟩
  rw [inner_graphField_conjugation, ← hB]
  exact haction.symm

theorem odd_linear_graph_field_involution_conjugacy
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (_hidentity : graphFieldAction n K A sigma ≠ 1)
    (hsquare : graphFieldAction n K A sigma ^ 2 = 1) :
    Even f ∧ (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ (f / 2) ∧
      ∃ H : GL (Fin n) K, graphFieldAction n K A sigma =
        innerDiagonalAction n K H * pslGraphFieldAut n K sigma *
          (innerDiagonalAction n K H)⁻¹ := by
  obtain ⟨hsigma, H, hH⟩ := graphField_involution_conjugacy n K hn A sigma hne hsquare
  obtain ⟨heven, hformula, hfixed⟩ :=
    CatalogueBLinearTwoDescent.quadraticField_parameters K p f hp hcard sigma hsigma hne
  exact ⟨heven, hformula, hfixed, H, hH⟩

end

end CFSG.ComponentClassification.CatalogueBGraphField
