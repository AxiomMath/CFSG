module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S8

open Matrix CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped commutatorElement

section General

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ext_mulVec {A B : Matrix ι ι K} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by rw [toLin'_apply, toLin'_apply, h v])

@[expose] def diagU : (ι → Kˣ) →* GL ι K :=
  (Units.map (diagonalRingHom ι K).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem coe_diagU (d : ι → Kˣ) :
    ((diagU d : GL ι K) : Matrix ι ι K) = diagonal fun i => (d i : K) := rfl

theorem diagU_mulVec (d : ι → Kˣ) (v : ι → K) :
    ((diagU d : GL ι K) : Matrix ι ι K) *ᵥ v = fun i => (d i : K) * v i := by
  rw [coe_diagU]
  funext i
  exact mulVec_diagonal _ _ i

theorem scalar_eq_diagU (c : Kˣ) :
    GeneralLinearGroup.scalar ι c = (diagU fun _ => c : GL ι K) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diagU, Matrix.scalar_apply]

@[expose] def permU (w : Equiv.Perm ι) : GL ι K where
  val := w.permMatrix K
  inv := w⁻¹.permMatrix K
  val_inv := by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  inv_val := by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem permU_mulVec (w : Equiv.Perm ι) (v : ι → K) :
    ((permU w : GL ι K) : Matrix ι ι K) *ᵥ v = v ∘ w :=
  permMatrix_mulVec ..

theorem permU_inv_mulVec (w : Equiv.Perm ι) (v : ι → K) :
    (((permU w)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = v ∘ ⇑w⁻¹ :=
  permMatrix_mulVec ..

theorem permU_mul_diagU_mul_inv (w : Equiv.Perm ι) (d : ι → Kˣ) :
    permU w * diagU d * (permU w)⁻¹ = (diagU (d ∘ w) : GL ι K) := by
  apply Units.ext
  apply ext_mulVec
  intro v
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, permU_inv_mulVec,
    diagU_mulVec, permU_mulVec, diagU_mulVec]
  funext i
  simp

theorem glFieldAut_diagU (σ : K ≃+* K) (d : ι → Kˣ) :
    glFieldAut ι K σ (diagU d) = diagU fun i => Units.map σ.toRingHom.toMonoidHom (d i) := by
  apply Units.ext
  ext i j
  change σ ((diagU d : Matrix ι ι K) i j) = _
  rw [coe_diagU, coe_diagU, diagonal_apply, diagonal_apply]
  split_ifs <;> simp

theorem glFieldAut_permU (σ : K ≃+* K) (w : Equiv.Perm ι) :
    glFieldAut ι K σ (permU w) = permU w := by
  apply Units.ext
  ext i j
  change σ ((w.permMatrix K) i j) = (w.permMatrix K) i j
  have h : ∀ x : K, (x = 0 ∨ x = 1) → σ x = x := by
    rintro x (rfl | rfl) <;> simp
  refine h _ ?_
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  split_ifs <;> simp

end General

section Stated

variable (K : Type) [Field K]

@[expose] def dil (μ : Kˣ) : GL (Fin 4 ⊕ Fin 4) K :=
  diagU (Sum.elim (fun _ => μ) fun _ => 1)

@[expose] def tor (a : Fin 4 → Kˣ) : GL (Fin 4 ⊕ Fin 4) K :=
  diagU (Sum.elim a fun i => (a i)⁻¹)

variable {K}

theorem quadPlus_dil (μ : Kˣ) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((dil K μ : Matrix _ _ K) *ᵥ v) = μ * quadPlus 4 K v := by
  rw [dil, diagU_mulVec, quadPlus_apply, quadPlus_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Units.val_one, one_mul]
  ring

theorem quadPlus_tor (a : Fin 4 → Kˣ) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((tor K a : Matrix _ _ K) *ᵥ v) = quadPlus 4 K v := by
  rw [tor, diagU_mulVec, quadPlus_apply, quadPlus_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h : ((a i : Kˣ) : K) * (((a i)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv (a i)
  linear_combination (v (.inl i) * v (.inr i)) * h

theorem dil_mul (μ μ' : Kˣ) : dil K (μ * μ') = dil K μ * dil K μ' := by
  rw [dil, dil, dil, ← map_mul]
  congr 1
  funext x
  cases x <;> simp

theorem glFieldAut_dil (σ : K ≃+* K) (μ : Kˣ) :
    glFieldAut (Fin 4 ⊕ Fin 4) K σ (dil K μ) = dil K (Units.map σ.toRingHom.toMonoidHom μ) := by
  rw [dil, dil, glFieldAut_diagU]
  congr 1
  funext x
  cases x <;> simp

theorem dil_mul_self (ν : Kˣ) :
    dil K (ν * ν) = GeneralLinearGroup.scalar _ ν * tor K (fun _ => ν) := by
  rw [scalar_eq_diagU, dil, tor, ← map_mul]
  congr 1
  funext x
  cases x <;> simp

@[expose] def wPerm : Equiv.Perm (Fin 4 ⊕ Fin 4) :=
  (Equiv.swap (.inl 0) (.inl 1) * Equiv.swap (.inl 0) (.inr 0) *
      Equiv.swap (.inl 0) (.inr 1)) *
    (Equiv.swap (.inl 2) (.inl 3) * Equiv.swap (.inl 2) (.inr 2) *
      Equiv.swap (.inl 2) (.inr 3))

theorem wPerm_inl_zero : wPerm (.inl 0) = .inr 1 := by decide
theorem wPerm_inr_zero : wPerm (.inr 0) = .inl 1 := by decide
theorem wPerm_inl_one : wPerm (.inl 1) = .inl 0 := by decide
theorem wPerm_inr_one : wPerm (.inr 1) = .inr 0 := by decide
theorem wPerm_inl_two : wPerm (.inl 2) = .inr 3 := by decide
theorem wPerm_inr_two : wPerm (.inr 2) = .inl 3 := by decide
theorem wPerm_inl_three : wPerm (.inl 3) = .inl 2 := by decide
theorem wPerm_inr_three : wPerm (.inr 3) = .inr 2 := by decide

variable (K) in
@[expose] def wU : GL (Fin 4 ⊕ Fin 4) K := permU wPerm

theorem quadPlus_wU (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K ((wU K : Matrix _ _ K) *ᵥ v) = quadPlus 4 K v := by
  rw [wU, permU_mulVec, quadPlus_apply, quadPlus_apply, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [Function.comp_apply, wPerm_inl_zero, wPerm_inr_zero, wPerm_inl_one, wPerm_inr_one,
    wPerm_inl_two, wPerm_inr_two, wPerm_inl_three, wPerm_inr_three]
  ring

theorem commutator_torAlt_wU (ν : Kˣ) :
    ⁅tor K ![1, ν, 1, ν], wU K⁆ = tor K (fun _ => ν) := by
  rw [commutatorElement_def, mul_assoc (tor K _ * wU K), mul_assoc, ← mul_assoc (wU K),
    tor, ← map_inv, wU, permU_mul_diagU_mul_inv, ← map_mul, tor]
  congr 1
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [wPerm_inl_zero, wPerm_inr_zero, wPerm_inl_one, wPerm_inr_one, wPerm_inl_two,
      wPerm_inr_two, wPerm_inl_three, wPerm_inr_three]

end Stated

section Coordinates

variable (K : Type) [Field K]

abbrev R8 : GL (Fin 4 ⊕ Fin 4) K ≃* GL (Fin (2 * 4)) K := reindexMatrixEquiv (plusIndexEquiv 4)

variable {K}

theorem glFieldAut_R8 (σ : K ≃+* K) (A : GL (Fin 4 ⊕ Fin 4) K) :
    glFieldAut (Fin (2 * 4)) K σ (R8 K A) = R8 K (glFieldAut (Fin 4 ⊕ Fin 4) K σ A) := by
  apply Units.ext
  ext i j
  rfl

theorem coordinateQuadPlus_R8 {A : GL (Fin 4 ⊕ Fin 4) K} {μ : K}
    (hA : ∀ v, quadPlus 4 K ((A : Matrix _ _ K) *ᵥ v) = μ * quadPlus 4 K v)
    (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K (matrixLinearEquiv (R8 K A) v) = μ * coordinateQuadPlus 4 K v := by
  obtain ⟨w, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective v
  rw [reindexMatrixEquiv_mulVec]
  change reindexQuadraticForm _ (quadPlus 4 K) (reindexVectorEquiv _ _) =
    μ * reindexQuadraticForm _ (quadPlus 4 K) (reindexVectorEquiv _ _)
  rw [reindexQuadraticForm_map, reindexQuadraticForm_map, hA]

theorem R8_mem_matrixIsometries {A : GL (Fin 4 ⊕ Fin 4) K}
    (hA : ∀ v, quadPlus 4 K ((A : Matrix _ _ K) *ᵥ v) = quadPlus 4 K v) :
    R8 K A ∈ matrixIsometries (coordinateQuadPlus 4 K) := by
  rw [mem_matrixIsometries_iff]
  intro v
  rw [coordinateQuadPlus_R8 (μ := 1) (fun v => by rw [hA, one_mul]), one_mul]

theorem det_R8 (A : GL (Fin 4 ⊕ Fin 4) K) :
    GeneralLinearGroup.det (R8 K A) = GeneralLinearGroup.det A := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, reindexMatrixEquiv_val,
    det_reindex_self]

theorem det_plusSwapMatrix :
    GeneralLinearGroup.det (CatalogueBOrthogonalPointPlusSwap.plusSwapMatrix 4 K (by norm_num)) =
      -1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, CatalogueBOrthogonalPointPlusSwap.coe_plusSwapMatrix,
    det_permutation, CatalogueBOrthogonalPointPlusSwap.plusSwapPerm,
    Equiv.Perm.sign_swap (by simp)]
  simp

theorem glFieldAut_plusSwapMatrix (σ : K ≃+* K) :
    glFieldAut (Fin 4 ⊕ Fin 4) K σ
        (CatalogueBOrthogonalPointPlusSwap.plusSwapMatrix 4 K (by norm_num)) =
      CatalogueBOrthogonalPointPlusSwap.plusSwapMatrix 4 K (by norm_num) := by
  have h : CatalogueBOrthogonalPointPlusSwap.plusSwapMatrix 4 K (by norm_num) =
      permU (CatalogueBOrthogonalPointPlusSwap.plusSwapPerm 4 (by norm_num)) := by
    apply Units.ext
    rfl
  rw [h, glFieldAut_permU]

end Coordinates

end CFSG.ComponentClassification.HarrisLit.T1.S8
