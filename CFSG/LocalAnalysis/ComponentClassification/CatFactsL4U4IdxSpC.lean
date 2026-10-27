module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Kron
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace IdxSp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

noncomputable abbrev R4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K ≃ₐ[K] Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindexAlgEquiv K K finSumFinEquiv

theorem R4_map (σ : K →+* K) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    R4 (M.map σ) = (R4 M).map σ := by
  simp only [coe_reindexAlgEquiv, reindex_apply, submatrix_map]

theorem det_R4 (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : (R4 M).det = M.det := by
  simp only [coe_reindexAlgEquiv, det_reindex_self]

theorem det_sp (g : StatedSp 2 K) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det = 1 := by
  have hsp : ((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈ TauCeti.GLSymplectic (Fin 2) K := by
    rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact g.2
  exact SymplecticGroup.det_eq_one (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp hsp)

@[expose] noncomputable def psi : StatedSp 2 K →* SpecialLinearGroup (Fin 4) K where
  toFun g := ⟨R4 ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
    by rw [det_R4, det_sp]⟩
  map_one' := by
    apply Subtype.ext
    change R4 (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
    rw [map_one]
  map_mul' x y := by
    apply Subtype.ext
    change R4 ((((x * y : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      R4 (((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
        R4 (((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    rw [← map_mul]
    rfl

theorem coe_psi (g : StatedSp 2 K) :
    ((psi g : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      R4 ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := rfl

theorem psi_injective : Function.Injective (psi : StatedSp 2 K →* SpecialLinearGroup (Fin 4) K) :=
  by
  intro x y hxy
  have h := congrArg (fun z : SpecialLinearGroup (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) hxy
  simp only [coe_psi] at h
  exact sp_ext (R4.injective h)

theorem conjAut_eq_one_of_scalar (B : gsp 2 K) {x : K}
    (hB : ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = x • 1) :
    conjAut 2 K B = 1 := by
  ext p
  obtain ⟨g, rfl⟩ := proj_surjective p
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp]
  have h : (B : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * (B : GL (Fin 2 ⊕ Fin 2) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hB, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  rw [h, mul_inv_cancel_right]

theorem conjAut_eq_of_smul (A B : gsp 2 K) {z : K}
    (hB : ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      z • ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K B = conjAut 2 K A := by
  ext p
  obtain ⟨g, rfl⟩ := proj_surjective p
  rw [conjAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, coe_conjSp]
  set A' : GL (Fin 2 ⊕ Fin 2) K := (A : GL (Fin 2 ⊕ Fin 2) K)
  set B' : GL (Fin 2 ⊕ Fin 2) K := (B : GL (Fin 2 ⊕ Fin 2) K)
  set g' : GL (Fin 2 ⊕ Fin 2) K := (g : GL (Fin 2 ⊕ Fin 2) K)
  have h : A' * g' * A'⁻¹ * B' = B' * g' := by
    apply Units.ext
    have e1 : ((A' * g' * A'⁻¹ * B' : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        z • ((A' * g' * A'⁻¹ * A' : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [Units.val_mul (A' * g' * A'⁻¹) B', hB, Matrix.mul_smul, ← Units.val_mul]
    have e2 : ((B' * g' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        z • ((A' * g' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [Units.val_mul, hB, Matrix.smul_mul, ← Units.val_mul]
    rw [e1, e2, inv_mul_cancel_right]
  rw [eq_mul_inv_of_mul_eq h]

theorem transpose_mul_formJ {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {d : K} (hd : d ≠ 0)
    (hAA : A * A = d • 1) (hμ : Aᵀ * formJ 2 K * A = d • formJ 2 K) :
    Aᵀ * formJ 2 K = formJ 2 K * A := by
  have h1 : Aᵀ * formJ 2 K * A * A = d • (formJ 2 K * A) := by
    rw [hμ, Matrix.smul_mul]
  rw [Matrix.mul_assoc (Aᵀ * formJ 2 K), hAA, Matrix.mul_smul, Matrix.mul_one] at h1
  have h2 := congrArg (fun M => d⁻¹ • M) h1
  simp only [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  exact h2

theorem mul_eq_zero_of_mem_gsp (h2 : (2 : K) ≠ 0) {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {d : K} (hd : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d) (hAA : A * A = d • 1)
    (hμ : Aᵀ * formJ 2 K * A = d • formJ 2 K) {x z : K} (hB : B = x • 1 + z • A) {m : K}
    (hBm : Bᵀ * formJ 2 K * B = m • formJ 2 K) : x * z = 0 := by
  by_contra hxz
  have hAJ := transpose_mul_formJ hd hAA hμ
  have e1 : Bᵀ * formJ 2 K = x • formJ 2 K + z • (formJ 2 K * A) := by
    rw [hB, transpose_add, transpose_smul, transpose_smul, transpose_one, Matrix.add_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hAJ]
  have e2 : formJ 2 K * A * A = d • formJ 2 K := by
    rw [Matrix.mul_assoc, hAA, Matrix.mul_smul, Matrix.mul_one]
  have e : Bᵀ * formJ 2 K * B =
      (x ^ 2 + z ^ 2 * d) • formJ 2 K + (2 * x * z) • (formJ 2 K * A) := by
    rw [e1, hB]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [e2]
    module
  rw [e] at hBm
  set c := (m - (x ^ 2 + z ^ 2 * d)) / (2 * x * z) with hc
  have h2xz : (2 * x * z) ≠ 0 := by
    rw [mul_assoc]
    exact mul_ne_zero h2 hxz
  have hJA : formJ 2 K * A = c • formJ 2 K := by
    have h3 : (2 * x * z) • (formJ 2 K * A) = (m - (x ^ 2 + z ^ 2 * d)) • formJ 2 K := by
      rw [sub_smul, ← hBm, add_sub_cancel_left]
    have h4 := congrArg (fun M => (2 * x * z)⁻¹ • M) h3
    simp only [smul_smul, inv_mul_cancel₀ h2xz, one_smul] at h4
    rw [h4, hc, div_eq_inv_mul]
  have hA : A = c • 1 := by
    have h5 := congrArg (fun M => -(formJ 2 K) * M) hJA
    simp only [← Matrix.mul_assoc, Matrix.neg_mul, formJ_mul_formJ, neg_neg, Matrix.one_mul,
      Matrix.mul_smul] at h5
    rw [h5]
  rw [hA, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hAA
  have h6 := congrFun (congrFun hAA (Sum.inl 0)) (Sum.inl 0)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h6
  exact hdsq c (by rw [sq]; exact h6)

end IdxSp

end CFSG.ComponentClassification.CatFactsL4U4
