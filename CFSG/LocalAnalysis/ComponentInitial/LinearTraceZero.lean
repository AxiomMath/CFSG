module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

variable (k : Type*) [Field k]

abbrev traceZeroMatrices : Submodule k (Matrix (Fin 2) (Fin 2) k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)

variable {k} in
theorem mem_traceZeroMatrices {X : Matrix (Fin 2) (Fin 2) k} :
    X ∈ traceZeroMatrices k ↔ X 0 0 + X 1 1 = 0 := by
  rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_fin_two]

variable {k} in
theorem conj_mem_traceZeroMatrices (g : Matrix.SpecialLinearGroup (Fin 2) k)
    {X : Matrix (Fin 2) (Fin 2) k} (hX : X ∈ traceZeroMatrices k) :
    (g : Matrix (Fin 2) (Fin 2) k) * X *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) ∈
      traceZeroMatrices k := by
  rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hX ⊢
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul, hX]

@[expose] noncomputable def traceZeroConj :
    Matrix.SpecialLinearGroup (Fin 2) k →* LinearMap.GeneralLinearGroup k (traceZeroMatrices k) :=
  MonoidHom.toHomUnits
    { toFun g :=
        { toFun X := ⟨(g : Matrix (Fin 2) (Fin 2) k) * X *
              ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k),
            conj_mem_traceZeroMatrices g X.2⟩
          map_add' X Y := Subtype.ext (by simp [mul_add, add_mul])
          map_smul' c X := Subtype.ext (by simp) }
      map_one' := LinearMap.ext fun X => Subtype.ext (by simp)
      map_mul' g h := LinearMap.ext fun X => Subtype.ext (by simp [mul_assoc]) }

@[simp] theorem traceZeroConj_apply (g : Matrix.SpecialLinearGroup (Fin 2) k)
    (X : traceZeroMatrices k) :
    (((traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X :
      traceZeroMatrices k) : Matrix (Fin 2) (Fin 2) k) =
      (g : Matrix (Fin 2) (Fin 2) k) * X *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) :=
  rfl

section Proof

variable {k}

private def upperUnip (t : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def lowerUnip (t : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

variable (k) in
private def opP : traceZeroMatrices k →ₗ[k] traceZeroMatrices k :=
  (traceZeroConj k (upperUnip 1) : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) -
    (traceZeroConj k (upperUnip (-1)) : traceZeroMatrices k →ₗ[k] traceZeroMatrices k)

variable (k) in
private def opQ : traceZeroMatrices k →ₗ[k] traceZeroMatrices k :=
  (traceZeroConj k (lowerUnip 1) : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) -
    (traceZeroConj k (lowerUnip (-1)) : traceZeroMatrices k →ₗ[k] traceZeroMatrices k)

@[simp] private theorem coe_upperUnip (t : k) :
    ((upperUnip t : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, t; 0, 1] :=
  rfl

@[simp] private theorem coe_lowerUnip (t : k) :
    ((lowerUnip t : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; t, 1] :=
  rfl

private theorem opP_apply (X : traceZeroMatrices k) :
    ((opP k X : traceZeroMatrices k) : Matrix (Fin 2) (Fin 2) k) =
      !![2 * X.1 1 0, -4 * X.1 0 0; 0, -2 * X.1 1 0] := by
  have hX := mem_traceZeroMatrices.1 X.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    first | ring1 | linear_combination 2 * hX

private theorem opQ_apply (X : traceZeroMatrices k) :
    ((opQ k X : traceZeroMatrices k) : Matrix (Fin 2) (Fin 2) k) =
      !![-2 * X.1 0 1, 0; 4 * X.1 0 0, 2 * X.1 0 1] := by
  have hX := mem_traceZeroMatrices.1 X.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opQ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    first | ring1 | linear_combination -2 * hX

variable (k) in
private def tzE : traceZeroMatrices k :=
  ⟨!![0, 1; 0, 0], mem_traceZeroMatrices.2 (by simp)⟩

variable (k) in
private def tzH : traceZeroMatrices k :=
  ⟨!![1, 0; 0, -1], mem_traceZeroMatrices.2 (by simp)⟩

variable (k) in
private def tzF : traceZeroMatrices k :=
  ⟨!![0, 0; 1, 0], mem_traceZeroMatrices.2 (by simp)⟩

private theorem tz_decomp (X : traceZeroMatrices k) :
    X = X.1 0 0 • tzH k + X.1 0 1 • tzE k + X.1 1 0 • tzF k := by
  have hX := mem_traceZeroMatrices.1 X.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tzE, tzH, tzF]
  linear_combination hX

private theorem tzE_ne_zero : tzE k ≠ 0 := fun h => by
  simpa [tzE] using congrArg (fun Y : traceZeroMatrices k => Y.1 0 1) h

private theorem tzH_ne_zero : tzH k ≠ 0 := fun h => by
  simpa [tzH] using congrArg (fun Y : traceZeroMatrices k => Y.1 0 0) h

private theorem opP_tzE : opP k (tzE k) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opP_apply, tzE]

private theorem opP_tzH : opP k (tzH k) = (-4 : k) • tzE k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opP_apply, tzE, tzH]

private theorem opP_tzF : opP k (tzF k) = (2 : k) • tzH k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opP_apply, tzF, tzH]

private theorem opQ_tzE : opQ k (tzE k) = (-2 : k) • tzH k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opQ_apply, tzE, tzH]

private theorem opQ_tzH : opQ k (tzH k) = (4 : k) • tzF k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opQ_apply, tzF, tzH]

private theorem opQ_tzF : opQ k (tzF k) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opQ_apply, tzF]

private theorem four_ne_zero_of_two_ne_zero (h2 : (2 : k) ≠ 0) : (4 : k) ≠ 0 := by
  rw [show (4 : k) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

private theorem opP_eq_zero (h2 : (2 : k) ≠ 0) {X : traceZeroMatrices k} (h : opP k X = 0) :
    X.1 1 0 = 0 ∧ X.1 0 0 = 0 := by
  have h4 := four_ne_zero_of_two_ne_zero h2
  have h' := congrArg (fun Y : traceZeroMatrices k => (Y : Matrix (Fin 2) (Fin 2) k)) h
  simp only [opP_apply] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  simp [h2, h4] at h00 h01
  exact ⟨h00, h01⟩

private theorem opQ_eq_zero (h2 : (2 : k) ≠ 0) {X : traceZeroMatrices k} (h : opQ k X = 0) :
    X.1 0 1 = 0 ∧ X.1 0 0 = 0 := by
  have h4 := four_ne_zero_of_two_ne_zero h2
  have h' := congrArg (fun Y : traceZeroMatrices k => (Y : Matrix (Fin 2) (Fin 2) k)) h
  simp only [opQ_apply] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h10 := congrFun (congrFun h' 1) 0
  simp [h2, h4] at h00 h10
  exact ⟨h00, h10⟩

private theorem eq_smul_tzE {Y : traceZeroMatrices k} (h10 : Y.1 1 0 = 0) (h00 : Y.1 0 0 = 0) :
    Y = Y.1 0 1 • tzE k := by
  conv_lhs => rw [tz_decomp Y]
  simp [h10, h00]

private theorem eq_smul_tzF {Y : traceZeroMatrices k} (h01 : Y.1 0 1 = 0) (h00 : Y.1 0 0 = 0) :
    Y = Y.1 1 0 • tzF k := by
  conv_lhs => rw [tz_decomp Y]
  simp [h01, h00]

section Commute

variable {A : traceZeroMatrices k →ₗ[k] traceZeroMatrices k}
  (hA : ∀ g X, (traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) (A X) =
    A ((traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X))
include hA

private theorem opP_comm (X : traceZeroMatrices k) : opP k (A X) = A (opP k X) := by
  simp only [opP, LinearMap.sub_apply, map_sub, hA]

private theorem opQ_comm (X : traceZeroMatrices k) : opQ k (A X) = A (opQ k X) := by
  simp only [opQ, LinearMap.sub_apply, map_sub, hA]

private theorem exists_eq_smul_id (h2 : (2 : k) ≠ 0) : ∃ a : k, A = a • LinearMap.id := by
  obtain ⟨a, hE⟩ : ∃ a : k, A (tzE k) = a • tzE k := by
    obtain ⟨h10, h00⟩ := opP_eq_zero h2 (show opP k (A (tzE k)) = 0 by
      rw [opP_comm hA, opP_tzE, map_zero])
    exact ⟨_, eq_smul_tzE h10 h00⟩
  obtain ⟨b, hF⟩ : ∃ b : k, A (tzF k) = b • tzF k := by
    obtain ⟨h01, h00⟩ := opQ_eq_zero h2 (show opQ k (A (tzF k)) = 0 by
      rw [opQ_comm hA, opQ_tzF, map_zero])
    exact ⟨_, eq_smul_tzF h01 h00⟩
  have hH : A (tzH k) = b • tzH k := by
    have h := opP_comm hA (tzF k)
    rw [hF, map_smul, opP_tzF, map_smul, smul_comm b] at h
    exact ((smul_right_inj h2).1 h).symm
  obtain rfl : a = b := by
    have h := opQ_comm hA (tzE k)
    rw [hE, map_smul, opQ_tzE, map_smul, hH, smul_comm a] at h
    have h' : a • tzH k = b • tzH k := (smul_right_inj (neg_ne_zero.2 h2)).1 h
    exact (smul_left_inj (tzH_ne_zero (k := k))).1 h'
  refine ⟨a, LinearMap.ext fun X => ?_⟩
  rw [tz_decomp X]
  simp only [map_add, map_smul, hE, hH, hF, LinearMap.smul_apply, LinearMap.id_apply]

end Commute

private theorem eq_zero_of_fixed (h2 : (2 : k) ≠ 0) {X : traceZeroMatrices k}
    (hX : ∀ g, (traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X = X) :
    X = 0 := by
  obtain ⟨h10, h00⟩ := opP_eq_zero h2 (show opP k X = 0 by simp [opP, hX])
  obtain ⟨h01, -⟩ := opQ_eq_zero h2 (show opQ k X = 0 by simp [opQ, hX])
  rw [tz_decomp X, h00, h01, h10]
  simp

private theorem eq_zero_of_invariant (h2 : (2 : k) ≠ 0) {φ : Module.Dual k (traceZeroMatrices k)}
    (hφ : ∀ g, φ ∘ₗ (traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) = φ) :
    φ = 0 := by
  have h4 := four_ne_zero_of_two_ne_zero h2
  have hφ' : ∀ g X,
      φ ((traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X) = φ X :=
    fun g X => LinearMap.congr_fun (hφ g) X
  have hP : ∀ X, φ (opP k X) = 0 := fun X => by simp [opP, hφ']
  have hQ : ∀ X, φ (opQ k X) = 0 := fun X => by simp [opQ, hφ']
  have hE : φ (tzE k) = 0 := by
    have h := hP (tzH k)
    rw [opP_tzH, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (neg_ne_zero.2 h4)
  have hH : φ (tzH k) = 0 := by
    have h := hP (tzF k)
    rw [opP_tzF, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left h2
  have hF : φ (tzF k) = 0 := by
    have h := hQ (tzH k)
    rw [opQ_tzH, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left h4
  refine LinearMap.ext fun X => ?_
  rw [tz_decomp X]
  simp [hE, hH, hF]

end Proof

theorem trace_zero_natural_SL2_commutant (hk : ringChar k ≠ 2) :
    (∀ A : LinearMap.GeneralLinearGroup k (traceZeroMatrices k),
      A ∈ Subgroup.centralizer ((traceZeroConj k).range : Set _) ↔
        ∃ a : kˣ, (A : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) = (a : k) • LinearMap.id) ∧
    {X : traceZeroMatrices k | ∀ d ∈ (traceZeroConj k).range,
        (d : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X = X} = {0} ∧
    {φ : Module.Dual k (traceZeroMatrices k) | ∀ d ∈ (traceZeroConj k).range,
        φ ∘ₗ (d : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) = φ} = {0} := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  refine ⟨fun A => ⟨fun hA => ?_, ?_⟩, ?_, ?_⟩
  · have hcomm : ∀ g X,
        (traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k)
            ((A : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X) =
          (A : traceZeroMatrices k →ₗ[k] traceZeroMatrices k)
            ((traceZeroConj k g : traceZeroMatrices k →ₗ[k] traceZeroMatrices k) X) := by
      intro g X
      have h := Subgroup.mem_centralizer_iff.1 hA _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)
      simpa using LinearMap.congr_fun (congrArg Units.val h) X
    obtain ⟨a, ha⟩ := exists_eq_smul_id hcomm h2
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h1 := A.mul_inv
      rw [ha, zero_smul, zero_mul] at h1
      exact tzE_ne_zero (by simpa using (LinearMap.congr_fun h1 (tzE k)).symm)
    exact ⟨Units.mk0 a ha0, ha⟩
  · rintro ⟨a, ha⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro d -
    ext X : 2
    simp [ha]
  · ext X
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hX => eq_zero_of_fixed h2 fun g => hX _ (MonoidHom.mem_range.2 ⟨g, rfl⟩), ?_⟩
    rintro rfl d -
    exact map_zero _
  · ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hφ => eq_zero_of_invariant h2 fun g => hφ _ (MonoidHom.mem_range.2 ⟨g, rfl⟩),
      ?_⟩
    rintro rfl d -
    exact LinearMap.zero_comp _

end CFSG.LocalAnalysis.ComponentInitial
