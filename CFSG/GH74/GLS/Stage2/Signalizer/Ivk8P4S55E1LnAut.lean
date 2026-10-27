module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1LnRad
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1LnVec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem exists_smul_of_proj_eq {g h : SpecialLinearGroup (Fin n) K}
    (e : proj n K g = proj n K h) :
    ∃ c : K, c ≠ 0 ∧ (h : Matrix (Fin n) (Fin n) K) = c • (g : Matrix (Fin n) (Fin n) K) := by
  have h1 : g⁻¹ * h ∈ scalars n K := QuotientGroup.eq.mp e
  obtain ⟨c, -, hc⟩ := h1
  refine ⟨(c : K), c.ne_zero, ?_⟩
  have h3 : (h : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ * h : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [h3, hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem conj_map_one_add_vecMulVec (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hA : A * A' = 1) (v φ : Fin n → K) :
    A * (1 + vecMulVec v φ).map σ * A' =
      1 + vecMulVec (A *ᵥ fun i => σ (v i)) ((fun i => σ (φ i)) ᵥ* A') := by
  have h1 : (1 + vecMulVec v φ).map σ =
      1 + vecMulVec (fun i => σ (v i)) (fun i => σ (φ i)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, vecMulVec_apply, map_add, map_mul,
      Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hA, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul]

theorem tvec_inv (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) :
    (tvec v φ h)⁻¹ = tvec v (-φ) (by rw [neg_dotProduct, h, neg_zero]) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvec, coe_tvec, Matrix.SpecialLinearGroup.coe_one]
  have h1 : vecMulVec v φ * vecMulVec v (-φ) = 0 := by
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]
  have h2 : vecMulVec v (-φ) = -vecMulVec v φ := by
    ext i j
    simp [vecMulVec_apply]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h1, h2]
  abel

theorem exists_conjAut_fieldAut_proj (A : GL (Fin n) K) (σ : K ≃+* K)
    (g : SpecialLinearGroup (Fin n) K) :
    ∃ y : SpecialLinearGroup (Fin n) K,
      (conjAut n K A * fieldAut n K σ) (proj n K g) = proj n K y ∧
      (y : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K).map σ * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
      (Matrix.SpecialLinearGroup.map σ.toRingHom g),
    by rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj],
    by
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      rfl⟩

theorem exists_conjAut_fieldAut_dualAut_proj (A : GL (Fin n) K) (σ : K ≃+* K)
    (g : SpecialLinearGroup (Fin n) K) :
    ∃ y : SpecialLinearGroup (Fin n) K,
      (conjAut n K A * fieldAut n K σ * dualAut n K) (proj n K g) = proj n K y ∧
      (y : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map σ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
      (Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.transpose g⁻¹)),
    by rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj],
    by
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      rfl⟩

theorem fix_tvec_of_conjAut_fieldAut (hn : 3 ≤ n) {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥)
    (hW1 : W ≠ ⊤) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hb : ∀ (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0), v ∈ W → (∀ w ∈ W, φ ⬝ᵥ w = 0) →
      (conjAut n K A * fieldAut n K σ) (proj n K (tvec v φ h)) = proj n K (tvec v φ h)) :
    (∀ c, σ c = c) ∧ ∃ l : K, l ≠ 0 ∧ (∀ w ∈ W, (A : Matrix (Fin n) (Fin n) K) *ᵥ w = l • w) ∧
      ∀ x, (A : Matrix (Fin n) (Fin n) K) *ᵥ x - l • x ∈ W := by
  have hAA' : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = 1 := Units.mul_inv A
  have hA'A : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)
      = 1 := Units.inv_mul A
  refine e0_core hn σ A ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) hA'A W hW0 hW1 ?_
  intro v hv φ hφ
  obtain ⟨y, hy1, hy2⟩ := exists_conjAut_fieldAut_proj A σ (tvec v φ (hφ v hv))
  have e := hb v φ (hφ v hv) hv hφ
  rw [hy1] at e
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_proj_eq e
  rw [hy2, coe_tvec] at hc
  refine ⟨c⁻¹, ?_⟩
  rw [← conj_map_one_add_vecMulVec σ A _ hAA' v φ]
  exact (eq_inv_smul_iff₀ hc0).mpr hc.symm

theorem false_of_fix_tvec_of_dualAut (hn : 3 ≤ n) {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥)
    (hW1 : W ≠ ⊤) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hb : ∀ (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0), v ∈ W → (∀ w ∈ W, φ ⬝ᵥ w = 0) →
      (conjAut n K A * fieldAut n K σ * dualAut n K) (proj n K (tvec v φ h)) =
        proj n K (tvec v φ h)) : False := by
  have hAA' : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = 1 := Units.mul_inv A
  refine e1_core hn σ A ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) W hW0 hW1 ?_
  intro v hv φ hφ
  obtain ⟨y, hy1, hy2⟩ := exists_conjAut_fieldAut_dualAut_proj A σ (tvec v φ (hφ v hv))
  have e := hb v φ (hφ v hv) hv hφ
  rw [hy1] at e
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_proj_eq e
  have hinv : (((tvec v φ (hφ v hv))⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + vecMulVec v (-φ) := by
    rw [tvec_inv, coe_tvec]
  rw [hy2, hinv, coe_tvec] at hc
  have hT : (1 + vecMulVec v (-φ))ᵀ = 1 + vecMulVec (-φ) v := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]
  rw [hT] at hc
  refine ⟨c⁻¹, ?_⟩
  have h1 := conj_map_one_add_vecMulVec σ A _ hAA' (-φ) v
  have h2 : (fun i => σ ((-φ) i)) = -fun i => σ (φ i) := by
    ext i
    simp
  rw [h2, Matrix.mulVec_neg] at h1
  rw [← h1]
  exact (eq_inv_smul_iff₀ hc0).mpr hc.symm

theorem conjAut_eq_one_of_scalar (hn : 1 ≤ n) {B : GL (Fin n) K} {c : K}
    (hB : (B : Matrix (Fin n) (Fin n) K) = c • 1) : conjAut n K B = 1 := by
  have : NeZero n := ⟨by omega⟩
  have h1 : (B : Matrix (Fin n) (Fin n) K) * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = 1 := Units.mul_inv B
  have hc : c ≠ 0 := by
    intro h0
    rw [hB, h0, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hBinv : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c⁻¹ • 1 := by
    rw [hB, smul_mul_assoc, one_mul] at h1
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => c⁻¹ • M) h1
    simpa [smul_smul, hc] using h2
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, hB, hBinv, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem pow_eq_one_of_fix_tvec [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r] (hn : 3 ≤ n)
    {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (b : MulAut (projectiveSL n K))
    (hb : ∀ (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0), v ∈ W → (∀ w ∈ W, φ ⬝ᵥ w = 0) →
      b (proj n K (tvec v φ h)) = proj n K (tvec v φ h)) : b ^ r = 1 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨A, σ, ε, hε, hbeq⟩ := (automorphism_generation (K := K) (n := n) hn).2 b
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hbeq
    rw [hbeq] at hb ⊢
    obtain ⟨hσ, l, hl0, hAW, hAx⟩ := fix_tvec_of_conjAut_fieldAut hn hW0 hW1 A σ hb
    have hσ1 : σ = 1 := RingEquiv.ext hσ
    rw [hσ1, map_one, mul_one, ← map_pow]
    refine conjAut_eq_one_of_scalar (by omega) (c := l ^ r) ?_
    set D : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) - l • 1 with hD
    have hDW : ∀ x, D *ᵥ x ∈ W := fun x => by
      rw [hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact hAx x
    have hD0 : ∀ w ∈ W, D *ᵥ w = 0 := fun w hw => by
      rw [hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAW w hw, sub_self]
    have hDD : D * D = 0 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hD0 _ (hDW x), map_zero,
        LinearMap.zero_apply]
    have hDr : D ^ r = 0 := by
      have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
      rw [show r = 2 + (r - 2) by omega, pow_add, pow_two, hDD, zero_mul]
    have hAD : (A : Matrix (Fin n) (Fin n) K) = l • 1 + D := by rw [hD]; abel
    rw [Units.val_pow_eq_pow_val, hAD, add_pow_char_of_commute r
      ((Commute.one_left D).smul_left l), hDr, add_zero, smul_pow, one_pow]
  · exfalso
    rw [pow_one] at hbeq
    rw [hbeq] at hb
    exact false_of_fix_tvec_of_dualAut hn hW0 hW1 A σ hb

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
