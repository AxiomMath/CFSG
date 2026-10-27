module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangHerm
public import CFSG.GH74.GLS.Stage4.T2F1LocH90

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem prod_pow_eq_one_of_swap {K : Type} [Field K] (σ : K ≃+* K) {c a b : K} {m : ℕ}
    (hm : Even m) (hσm : σ ^ m = 1) (ha : a = c * σ b) (hb : b = c * σ a) (ha0 : a ≠ 0) :
    ∏ i ∈ Finset.range m, (σ ^ i) c = 1 := by
  classical
  let x : ℕ → K := fun k => if Even k then a else b
  have hx : ∀ k, x k = c * σ (x (k + 1)) := by
    intro k
    by_cases hk : Even k
    · have hk' : ¬ Even (k + 1) := by
        rw [Nat.even_add_one]
        exact not_not.mpr hk
      simp only [x, if_pos hk, if_neg hk']
      exact ha
    · have hk' : Even (k + 1) := by
        rw [Nat.even_add_one]
        exact hk
      simp only [x, if_neg hk, if_pos hk']
      exact hb
  have key : ∀ k, a = (∏ i ∈ Finset.range k, (σ ^ i) c) * (σ ^ k) (x k) := by
    intro k
    induction k with
    | zero => simp [x]
    | succ k ih =>
      have h1 : (σ ^ k) (x k) = (σ ^ k) c * (σ ^ (k + 1)) (x (k + 1)) := by
        rw [hx k, map_mul, pow_succ]
        rfl
      rw [Finset.prod_range_succ, mul_assoc, ← h1]
      exact ih
  have hm0 := key m
  have hxm : x m = a := by simp [x, hm]
  rw [hxm, hσm, RingAut.one_apply] at hm0
  have h2 : (∏ i ∈ Finset.range m, (σ ^ i) c) * a = 1 * a := by
    rw [one_mul]
    exact hm0.symm
  exact mul_right_cancel₀ ha0 h2

theorem exists_conj_of_sq_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) {σ : K ≃+* K}
    (hσ : Even (orderOf σ)) (A : GL (Fin n) K)
    (hsq : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = fieldAut n K (σ * σ)) :
    ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ * dualAut n K =
      conjAut n K H * (fieldAut n K σ * dualAut n K) * (conjAut n K H)⁻¹ := by
  classical
  rw [sq_conjAut_fieldAut_dualAut] at hsq
  have hX : conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose A)) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one]
    exact mul_right_cancel (b := fieldAut n K (σ * σ)) (by rw [hsq, one_mul])
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hX
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hM
  have hmap : ∀ X : GL (Fin n) K, ((GeneralLinearGroup.map (σ : K →+* K) X : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (X : Matrix (Fin n) (Fin n) K).map σ := fun _ => rfl
  have hcM : (c : K) • (1 : Matrix (Fin n) (Fin n) K) =
      M * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ := by
    have hscal : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [smul_one_eq_diagonal]
      rfl
    have h : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((A * GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose A) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hc
    rw [hscal, Units.val_mul, hmap, GeneralLinearGroup.coe_inverseTranspose] at h
    exact h
  have hN : (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ * conjTr σ M = 1 := by
    rw [conjTr_eq_map_transpose]
    change (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map (σ : K →+* K) *
      (Mᵀ).map (σ : K →+* K) = 1
    rw [← Matrix.map_mul, ← transpose_mul, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      transpose_one]
    simp
  have hA : M = (c : K) • conjTr σ M := by
    calc M = M * ((((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ *
          conjTr σ M) := by rw [hN, Matrix.mul_one]
      _ = ((c : K) • (1 : Matrix (Fin n) (Fin n) K)) * conjTr σ M := by
          rw [← Matrix.mul_assoc, ← hcM]
      _ = (c : K) • conjTr σ M := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hM0 : M ≠ 0 := by
    intro h0
    have hu : IsUnit M.det := Matrix.isUnits_det_units A
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    rw [h0, Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have hcTr : conjTr σ M = (c : K)⁻¹ • M := by
    conv_rhs => rw [hA]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hM0 (Matrix.ext fun i j => hcon i j)
  have hent : ∀ i j, M i j = c * σ (M j i) := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [conjTr] using this
  have hnorm : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (c : K) = 1 :=
    prod_pow_eq_one_of_swap σ hσ (pow_orderOf_eq_one σ) (hent i₀ j₀) (hent j₀ i₀) hij
  have : Finite (K ≃+* K) := finite_ringEquiv K
  obtain ⟨y, hy0, hy⟩ := CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField σ
    (r := orderOf σ) rfl (x := (c : K)⁻¹)
    (by simp only [map_inv₀, Finset.prod_inv_distrib, hnorm, inv_one])
  have hσy : σ y = c * y := by
    have h1 : (c : K) * ((c : K)⁻¹ * σ y) = c * y := by rw [hy]
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h1
    exact h1
  set B : Matrix (Fin n) (Fin n) K := y • M with hB
  have hBherm : conjTr σ B = B := by
    rw [hB, conjTr_smul, hσy, hcTr, smul_smul]
    congr 1
    field_simp
  have hBdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hy0) (Matrix.isUnits_det_units A).ne_zero
  obtain ⟨H, hHH⟩ := exists_mul_conjTr_eq (exists_sq_fixed_ne hσ) hBherm hBdet
  refine ⟨H, ?_⟩
  have hconj : conjAut n K H * (fieldAut n K σ * dualAut n K) * (conjAut n K H)⁻¹ =
      conjAut n K (H * GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose H⁻¹)) * fieldAut n K σ * dualAut n K := by
    rw [← map_inv, mul_assoc, mul_assoc, dualAut_mul_conjAut, ← mul_assoc (fieldAut n K σ),
      fieldAut_mul_conjAut, map_mul]
    simp only [mul_assoc]
  have hY : H * GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose H⁻¹) =
      GeneralLinearGroup.scalar (Fin n) (Units.mk0 y hy0) * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hmap, GeneralLinearGroup.coe_inverseTranspose, inv_inv,
      ← conjTr_eq_map_transpose, hHH, hB]
    have hscaly : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 y hy0) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = y • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [smul_one_eq_diagonal]
      rfl
    rw [hscaly, Matrix.smul_mul, Matrix.one_mul]
  rw [hconj, hY, map_mul, conjAut_scalar, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang
