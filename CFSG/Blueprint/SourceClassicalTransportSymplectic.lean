module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix
open LinearMap (BilinForm)

section Isometry

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] def matrixIsometry (G : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {A | (A : Matrix ι ι K)ᵀ * G * A = G}
  mul_mem' {A B} hA hB := by
    change ((A * B : GL ι K) : Matrix ι ι K)ᵀ * G * ((A * B : GL ι K) : Matrix ι ι K) = G
    rw [Units.val_mul, transpose_mul]
    calc (B : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ * G * ((A : Matrix ι ι K) * B)
        = (B : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * G * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hA, hB]
  one_mem' := by
    change ((1 : GL ι K) : Matrix ι ι K)ᵀ * G * ((1 : GL ι K) : Matrix ι ι K) = G
    rw [Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' {A} hA := by
    change ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * G * ((A⁻¹ : GL ι K) : Matrix ι ι K) = G
    have h1 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * G * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * G * A) *
            ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA]
      _ = ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * G *
            ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_matrixIsometry {G : Matrix ι ι K} {A : GL ι K} :
    A ∈ matrixIsometry G ↔ (A : Matrix ι ι K)ᵀ * G * A = G :=
  Iff.rfl

theorem map_sourceIsometry_bilin (b : Basis ι K V) (B : BilinForm K V) :
    (sourceIsometry fun x y => B x y).map (sourceGLEquiv b).toMonoidHom =
      matrixIsometry (BilinForm.toMatrix b B) := by
  ext A
  rw [Subgroup.mem_map_equiv, mem_matrixIsometry]
  set g := (sourceGLEquiv b).symm A
  have hg : LinearMap.toMatrix b b (g : Module.End K V) = A := by
    rw [← coe_sourceGLEquiv, MulEquiv.apply_symm_apply]
  change (∀ x y, B ((g : Module.End K V) x) ((g : Module.End K V) y) = B x y) ↔ _
  rw [← hg, ← BilinForm.toMatrix_comp]
  constructor
  · intro h
    congr 1
    ext x y
    exact h x y
  · intro h x y
    have h' := (BilinForm.toMatrix b).injective h
    exact congrArg (fun B' : BilinForm K V => B' x y) h'

end Isometry

abbrev sourceSpJ (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks 0 1 (-1) 0

theorem statedSp_eq_matrixIsometry (n : ℕ) (K : Type) [Field K] :
    StatedSp n K = matrixIsometry (sourceSpJ n K) := by
  rw [StatedSp]
  exact Subgroup.closure_eq (matrixIsometry (sourceSpJ n K))

theorem sourceSpJ_eq_neg_J (n : ℕ) (K : Type) [Field K] : sourceSpJ n K = -Matrix.J (Fin n) K := by
  rw [sourceSpJ, Matrix.J, fromBlocks_neg, neg_zero, neg_neg]

theorem toBilin'_sourceSpJ_self (n : ℕ) (K : Type) [Field K] (x : Fin n ⊕ Fin n → K) :
    Matrix.toBilin' (sourceSpJ n K) x x = 0 := by
  rw [Matrix.toBilin'_apply]
  simp [Fintype.sum_sum_type, fromBlocks, Matrix.one_apply]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sourceClassicalModel_of_stated_PSp {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSp n p f) : SourceClassicalModel X .PSp n p f := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  set B : BilinForm K (Fin n ⊕ Fin n → K) := Matrix.toBilin' (sourceSpJ n K) with hB
  have hdet : IsUnit (sourceSpJ n K).det := by
    rw [sourceSpJ_eq_neg_J, det_neg]
    exact (isUnit_neg_one.pow _).mul (Matrix.isUnit_det_J (Fin n) K)
  have hnd : B.Nondegenerate :=
    BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet.ne_zero
  have hmat : BilinForm.toMatrix (Pi.basisFun K (Fin n ⊕ Fin n)) B = sourceSpJ n K := by
    rw [BilinForm.toMatrix_basisFun, hB, BilinForm.toMatrix'_toBilin']
  refine ⟨hadm, K, inferInstance, inferInstance, Fin n ⊕ Fin n → K, inferInstance, inferInstance,
    inferInstance, sourceIsometry fun x y => B x y, ⟨e.trans (quotientInfCongr
      (sourceGLEquiv (Pi.basisFun K (Fin n ⊕ Fin n))).symm ?_ ?_)⟩, hK, ?_, B,
    fun x => toBilin'_sourceSpJ_self n K x, ?_, rfl⟩
  · rw [statedSp_eq_matrixIsometry, ← hmat,
      ← map_sourceIsometry_bilin (Pi.basisFun K (Fin n ⊕ Fin n)) B, Subgroup.map_map]
    simp
  · rw [← map_sourceScalars_sourceGLEquiv (Pi.basisFun K (Fin n ⊕ Fin n)), Subgroup.map_map]
    simp
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  · ext x
    refine ⟨fun hx => Set.mem_singleton_iff.mpr (hnd.1 x hx), fun hx y => ?_⟩
    rw [Set.mem_singleton_iff.mp hx, map_zero, LinearMap.zero_apply]

theorem stated_of_sourceClassicalModel_PSp {X : Type} [Group X] {n p f : ℕ}
    (h : SourceClassicalModel X .PSp n p f) : StatedClassicalModel X .PSp n p f := by
  obtain ⟨hadm, K, _, _, V, _, _, _, H, ⟨e⟩, hK, hV, B, halt, hrad, rfl⟩ := h
  have hsep : B.SeparatingLeft := fun x hx => by
    have : x ∈ {x | ∀ y, B x y = 0} := hx
    rwa [hrad] at this
  have hrefl : B.IsRefl := LinearMap.BilinForm.IsAlt.isRefl halt
  have hnd : B.Nondegenerate := ⟨hsep, fun y hy => hsep y fun x => hrefl _ _ (hy x)⟩
  obtain ⟨m, c, hm, hc0, hc1, hc2⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      B halt hnd
  obtain rfl : m = n := by omega
  have hG : BilinForm.toMatrix c B = sourceSpJ m K := by
    ext i j
    rw [BilinForm.toMatrix_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [hc0]
    · simp [hc2, Matrix.one_apply]
    · rw [← LinearMap.BilinForm.IsAlt.neg_eq halt, hc2]
      simp [Matrix.one_apply, eq_comm]
    · simp [hc1]
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans (quotientInfCongr (sourceGLEquiv c)
    (by rw [map_sourceIsometry_bilin, hG, statedSp_eq_matrixIsometry])
    (map_sourceScalars_sourceGLEquiv c))⟩⟩

end CFSG.Blueprint.EvenSource
