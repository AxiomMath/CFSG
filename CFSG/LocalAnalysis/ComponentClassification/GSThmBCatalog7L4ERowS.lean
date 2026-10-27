module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ERowSForm
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionNonsquareComponents

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

namespace Catalog7L4E

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

variable {k : Type} [Field k]

theorem dualAut_mul_self : dualAut 4 k * dualAut 4 k = 1 :=
  (standard_automorphism_transport (n := 4) (K := k)).2.2.2.1

theorem graphAlt_sq {Y : GL (Fin 4) k} (hY : (Y : Matrix (Fin 4) (Fin 4) k)ᵀ = -Y) :
    (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k Y⁻¹ * dualAut 4 k) = 1 := by
  rw [mul_assoc, ← mul_assoc (dualAut 4 k), dualAut_mul_conjAut, mul_assoc, dualAut_mul_self,
    mul_one, ← map_mul]
  have h : Y⁻¹ * GeneralLinearGroup.inverseTranspose Y⁻¹ =
      GeneralLinearGroup.scalar (Fin 4) (-1) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, inv_inv, hY,
      GeneralLinearGroup.coe_scalar, Matrix.mul_neg, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Units.val_neg, Units.val_one, Matrix.scalar_apply]
    ext i j
    simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [h, conjAut_scalar]

variable [Finite k]

theorem commute_graphAlt {Y M : GL (Fin 4) k} {μ : kˣ}
    (hM : (M : Matrix (Fin 4) (Fin 4) k)ᵀ * Y * M = (μ : k) • (Y : Matrix (Fin 4) (Fin 4) k)) :
    Commute (conjAut 4 k M) (conjAut 4 k Y⁻¹ * dualAut 4 k) := by
  change conjAut 4 k M * (conjAut 4 k Y⁻¹ * dualAut 4 k) =
    conjAut 4 k Y⁻¹ * dualAut 4 k * conjAut 4 k M
  rw [mul_assoc (conjAut 4 k Y⁻¹), dualAut_mul_conjAut, ← mul_assoc, ← mul_assoc, ← map_mul,
    ← map_mul]
  congr 1
  rw [conjAut_eq_conjAut_iff' (by norm_num)]
  refine ⟨μ, Units.ext ?_⟩
  set Ym : Matrix (Fin 4) (Fin 4) k := (Y : Matrix (Fin 4) (Fin 4) k) with hYm
  set Yi : Matrix (Fin 4) (Fin 4) k := ((Y⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
    with hYi
  set Mm : Matrix (Fin 4) (Fin 4) k := (M : Matrix (Fin 4) (Fin 4) k) with hMm
  set Mi : Matrix (Fin 4) (Fin 4) k := ((M⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
    with hMi
  have hYYi : Ym * Yi = 1 := by rw [hYm, hYi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYiY : Yi * Ym = 1 := by rw [hYm, hYi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMMi : Mm * Mi = 1 := by rw [hMm, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiTMT : Miᵀ * Mmᵀ = 1 := by rw [← transpose_mul, hMMi, transpose_one]
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose,
    GeneralLinearGroup.coe_scalar, ← hMi, ← hMm, ← hYi, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have h1 : Ym * Mm = (μ : k) • (Miᵀ * Ym) := by
    calc Ym * Mm = (Miᵀ * Mmᵀ) * Ym * Mm := by rw [hMiTMT, Matrix.one_mul]
      _ = Miᵀ * (Mmᵀ * Ym * Mm) := by simp only [Matrix.mul_assoc]
      _ = (μ : k) • (Miᵀ * Ym) := by rw [hM, Matrix.mul_smul]
  calc Mm * Yi = Yi * (Ym * Mm) * Yi := by rw [← Matrix.mul_assoc, hYiY, Matrix.one_mul]
    _ = Yi * ((μ : k) • (Miᵀ * Ym)) * Yi := by rw [h1]
    _ = (μ : k) • (Yi * Miᵀ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hYYi,
          Matrix.mul_one]


theorem graphAlt_not_mem (C Y : GL (Fin 4) k) :
    conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k C)⁻¹ ∉
      semilinearAutGroup 4 k := by
  intro h
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := k) (n := 4) (by norm_num)
  have hc : ∀ X : GL (Fin 4) k, conjAut 4 k X ∈ semilinearAutGroup 4 k := fun X =>
    mem_semilinearAutGroup_iff.mpr ⟨X, 1, by rw [map_one, mul_one]⟩
  have e : dualAut 4 k = (conjAut 4 k C * conjAut 4 k Y⁻¹)⁻¹ *
      (conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k C)⁻¹) *
      conjAut 4 k C := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (mul_mem (hc C) (hc _))) h) (hc C)

omit [Finite k] in
theorem graphAlt_coset (A C Y : GL (Fin 4) k) :
    (conjAut 4 k A * dualAut 4 k)⁻¹ *
        (conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k C)⁻¹) =
      conjAut 4 k (GeneralLinearGroup.inverseTranspose (A⁻¹ * C * Y⁻¹) * C⁻¹) := by
  have hδ : (dualAut 4 k)⁻¹ = dualAut 4 k := inv_eq_of_mul_eq_one_right dualAut_mul_self
  rw [_root_.mul_inv_rev, hδ, ← map_inv, ← map_inv]
  have e : dualAut 4 k * conjAut 4 k A⁻¹ * (conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) *
      conjAut 4 k C⁻¹) = dualAut 4 k * conjAut 4 k (A⁻¹ * C * Y⁻¹) * dualAut 4 k *
        conjAut 4 k C⁻¹ := by
    simp only [map_mul]
    group
  rw [e, dualAut_mul_conjAut]
  simp only [mul_assoc]
  rw [← mul_assoc (dualAut 4 k) (dualAut 4 k), dualAut_mul_self, one_mul, ← map_mul]

omit [Finite k] in
theorem det_inverseTranspose (X : GL (Fin 4) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose X) =
      (GeneralLinearGroup.det X)⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem exists_rowS_involution (ν : kˣ) [Fact (¬ IsSquare (ν : k))] (hk2 : ringChar k ≠ 2)
    (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k)) (C A : GL (Fin 4) k)
    (hsA : ∃ s : kˣ, GeneralLinearGroup.det A = s ^ 2) :
    ∃ x₀ : MulAut (projectiveSL 4 k), x₀ * x₀ = 1 ∧ x₀ ∉ semilinearAutGroup 4 k ∧
      Commute x₀ (conjAut 4 k C * conjAut 4 k (rowSU ν Ψ) * (conjAut 4 k C)⁻¹) ∧
      (∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)),
        Commute x₀ (conjAut 4 k C * conjAut 4 k (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) *
          (conjAut 4 k C)⁻¹)) ∧
      (conjAut 4 k A * dualAut 4 k)⁻¹ * x₀ ∈ OuterAutomorphisms.inner (projectiveSL 4 k) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have : Finite (extension (ν : k)) :=
    CatalogueBProjectiveInvolution.quadraticExtension_finite (ν : k)
  obtain ⟨sA, hsA⟩ := hsA
  set Y₁ := traceGram ν Ψ 1 with hY₁
  have hY₁0 : Y₁.det ≠ 0 := det_traceGram_ne_zero ν Ψ h2 one_ne_zero
  have hpf := det_eq_pfaffian_sq h2 (traceGram_transpose ν Ψ 1)
  set pf := Y₁ 0 1 * Y₁ 2 3 - Y₁ 0 2 * Y₁ 1 3 + Y₁ 0 3 * Y₁ 1 2 with hpfdef
  have hpf0 : pf ≠ 0 := by
    intro h
    rw [← hY₁, h] at hpf
    exact hY₁0 (by rw [hpf]; ring)
  obtain ⟨θ, hθ⟩ := FiniteField.unitsMap_norm_surjective k (extension (ν : k))
    (GeneralLinearGroup.det C * (sA * Units.mk0 pf hpf0)⁻¹)
  have hθN : Algebra.norm k (θ : extension (ν : k)) =
      (GeneralLinearGroup.det C : k) * ((sA : k) * pf)⁻¹ := by
    have := congrArg Units.val hθ
    simpa using this
  set Yθ := traceGram ν Ψ θ with hYθ
  have hYθ0 : Yθ.det ≠ 0 := det_traceGram_ne_zero ν Ψ h2 θ.ne_zero
  set Y : GL (Fin 4) k := Matrix.GeneralLinearGroup.mkOfDetNeZero Yθ hYθ0 with hYdef
  have hYm : (Y : Matrix (Fin 4) (Fin 4) k) = Yθ := rfl
  have hYt : (Y : Matrix (Fin 4) (Fin 4) k)ᵀ = -Y := by
    rw [hYm]
    exact traceGram_transpose ν Ψ θ
  refine ⟨conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k C)⁻¹, ?_,
    graphAlt_not_mem C Y, ?_, fun g => ?_, ?_⟩
  · have h := graphAlt_sq hYt
    calc conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k C)⁻¹ *
          (conjAut 4 k C * (conjAut 4 k Y⁻¹ * dualAut 4 k) * (conjAut 4 k C)⁻¹) =
          conjAut 4 k C * ((conjAut 4 k Y⁻¹ * dualAut 4 k) *
            (conjAut 4 k Y⁻¹ * dualAut 4 k)) * (conjAut 4 k C)⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · have h := commute_graphAlt (Y := Y) (M := rowSU ν Ψ) (μ := ν)
      (by rw [hYm]; exact traceGram_rowSU ν Ψ θ)
    have := (h.symm.conj (conjAut 4 k C))
    simpa only [mul_assoc] using this
  · have h := commute_graphAlt (Y := Y) (M := rowSPi ν Ψ (SpecialLinearGroup.toGL g)) (μ := 1)
      (by rw [hYm, Units.val_one, one_smul]; exact traceGram_invariant ν Ψ θ g)
    have := (h.symm.conj (conjAut 4 k C))
    simpa only [mul_assoc] using this
  · rw [graphAlt_coset, conjAut_mem_inner_iff (by norm_num)]
    refine ⟨1, ?_⟩
    rw [one_pow, map_mul, det_inverseTranspose, map_mul, map_mul, map_inv, map_inv, map_inv]
    have hdetY : (GeneralLinearGroup.det Y : k) = Algebra.norm k (θ : extension (ν : k)) ^ 2 *
        pf ^ 2 := by
      rw [GeneralLinearGroup.val_det_apply, hYm, hYθ, traceGram_eq, det_mul, det_transpose,
        det_rowSPi_scalar, ← hY₁, hpf]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    rw [hdetY, hsA, Units.val_pow_eq_pow_val, hθN]
    have hC0 : (GeneralLinearGroup.det C : k) ≠ 0 := (GeneralLinearGroup.det C).ne_zero
    have hs0 : (sA : k) ≠ 0 := sA.ne_zero
    field_simp

end Catalog7L4E

end CFSG.ComponentClassification.OddSelector
