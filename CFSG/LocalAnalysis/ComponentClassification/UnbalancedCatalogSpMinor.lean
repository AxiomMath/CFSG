module

public import CFSG.LinearAlgebra.ExteriorSquareMinorData
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix

namespace SpChain

variable {K : Type} [Field K]

variable (K) in
abbrev minorJ : Matrix (Fin 4) (Fin 4) K := CFSG.LinearAlgebra.exteriorSquareJ K

abbrev minorIdx : Fin 4 → Fin 4 × Fin 4 := CFSG.LinearAlgebra.exteriorSquareIndex

abbrev minorMap (g : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  CFSG.LinearAlgebra.exteriorSquareMinor g

theorem minorIdx_zero : minorIdx 0 = ((0 : Fin 4), (1 : Fin 4)) := rfl
theorem minorIdx_one : minorIdx 1 = ((0 : Fin 4), (2 : Fin 4)) := rfl
theorem minorIdx_two : minorIdx 2 = ((1 : Fin 4), (3 : Fin 4)) := rfl
theorem minorIdx_three : minorIdx 3 = ((2 : Fin 4), (3 : Fin 4)) := rfl

theorem minorMap_apply (g : Matrix (Fin 4) (Fin 4) K) (A B : Fin 4) :
    minorMap g A B = g (minorIdx A).1 (minorIdx B).1 * g (minorIdx A).2 (minorIdx B).2 -
      g (minorIdx A).1 (minorIdx B).2 * g (minorIdx A).2 (minorIdx B).1 :=
  rfl

theorem minorJ_apply (i j : Fin 4) : minorJ K i j = if i.val + j.val = 3 then 1 else 0 :=
  rfl

theorem minorJ_minorIdx (A : Fin 4) : minorJ K (minorIdx A).1 (minorIdx A).2 = 0 := by
  fin_cases A <;> simp [minorJ_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]

theorem mul_minorJ_mul_transpose_apply (g : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (g * minorJ K * gᵀ) i j = g i 0 * g j 3 + g i 1 * g j 2 + g i 2 * g j 1 + g i 3 * g j 0 := by
  simp [mul_apply, Fin.sum_univ_four, minorJ_apply]
  ring

theorem transpose_mul_minorJ_mul_apply (h : Matrix (Fin 4) (Fin 4) K) (k l : Fin 4) :
    (hᵀ * minorJ K * h) k l = h 0 k * h 3 l + h 1 k * h 2 l + h 2 k * h 1 l + h 3 k * h 0 l := by
  simp [mul_apply, Fin.sum_univ_four, minorJ_apply]
  ring

theorem minorJ_mul_self : minorJ K * minorJ K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four, minorJ_apply]

theorem minorJ_transpose : (minorJ K)ᵀ = minorJ K := by
  ext i j
  simp only [transpose_apply, minorJ_apply, add_comm]

abbrev glMat (g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  (g : Matrix (Fin 4) (Fin 4) K)

variable (K) in
@[expose] def antiSp : Subgroup (GL (Fin 4) K) where
  carrier := {g | (glMat g)ᵀ * minorJ K * glMat g = minorJ K}
  one_mem' := by
    change (1 : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * 1 = minorJ K
    rw [transpose_one, Matrix.one_mul, Matrix.mul_one]
  mul_mem' := by
    intro g h hg hh
    change (glMat g * glMat h)ᵀ * minorJ K * (glMat g * glMat h) = minorJ K
    calc (glMat g * glMat h)ᵀ * minorJ K * (glMat g * glMat h)
        _ = (glMat h)ᵀ * ((glMat g)ᵀ * minorJ K * glMat g) * glMat h := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = minorJ K := by
          rw [show (glMat g)ᵀ * minorJ K * glMat g = minorJ K from hg]
          exact hh
  inv_mem' := by
    intro g hg
    change (glMat g⁻¹)ᵀ * minorJ K * glMat g⁻¹ = minorJ K
    have hg' : (glMat g)ᵀ * minorJ K * glMat g = minorJ K := hg
    have hAB : glMat g * glMat g⁻¹ = 1 := g.mul_inv
    calc (glMat g⁻¹)ᵀ * minorJ K * glMat g⁻¹
        _ = (glMat g⁻¹)ᵀ * ((glMat g)ᵀ * minorJ K * glMat g) * glMat g⁻¹ := by rw [hg']
        _ = (glMat g * glMat g⁻¹)ᵀ * minorJ K * (glMat g * glMat g⁻¹) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = minorJ K := by rw [hAB, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_antiSp {g : GL (Fin 4) K} :
    g ∈ antiSp K ↔ (glMat g)ᵀ * minorJ K * glMat g = minorJ K :=
  Iff.rfl

theorem mul_minorJ_mul_transpose_of_mem {g : GL (Fin 4) K} (hg : g ∈ antiSp K) :
    glMat g * minorJ K * (glMat g)ᵀ = minorJ K := by
  have hg' : (glMat g)ᵀ * minorJ K * glMat g = minorJ K := hg
  have h1 : (minorJ K * (glMat g)ᵀ * minorJ K) * glMat g = 1 := by
    calc minorJ K * (glMat g)ᵀ * minorJ K * glMat g
        _ = minorJ K * ((glMat g)ᵀ * minorJ K * glMat g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', minorJ_mul_self]
  have h2 := mul_eq_one_comm.mp h1
  calc glMat g * minorJ K * (glMat g)ᵀ
      _ = (glMat g * (minorJ K * (glMat g)ᵀ * minorJ K)) * minorJ K := by
        simp only [Matrix.mul_assoc, minorJ_mul_self, Matrix.mul_one]
      _ = minorJ K := by rw [h2, Matrix.one_mul]

section Mul

theorem minor_mul_aux [CharP K 2] (g h : Matrix (Fin 4) (Fin 4) K) (i j k l : Fin 4)
    (hg : g i 0 * g j 3 + g i 1 * g j 2 + g i 2 * g j 1 + g i 3 * g j 0 = 0)
    (hh : h 0 k * h 3 l + h 1 k * h 2 l + h 2 k * h 1 l + h 3 k * h 0 l = 0) :
    (g * h) i k * (g * h) j l - (g * h) i l * (g * h) j k =
      (g i 0 * g j 1 - g i 1 * g j 0) * (h 0 k * h 1 l - h 1 k * h 0 l) +
      (g i 0 * g j 2 - g i 2 * g j 0) * (h 0 k * h 2 l - h 2 k * h 0 l) +
      (g i 1 * g j 3 - g i 3 * g j 1) * (h 1 k * h 3 l - h 3 k * h 1 l) +
      (g i 2 * g j 3 - g i 3 * g j 2) * (h 2 k * h 3 l - h 3 k * h 2 l) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [mul_apply, Fin.sum_univ_four]
  set u := g i 0 * g j 3 - g i 3 * g j 0
  set w := h 0 k * h 3 l - h 3 k * h 0 l
  set α := g i 3 * g j 0 + g i 2 * g j 1
  set β := h 3 k * h 0 l + h 2 k * h 1 l
  set Rh := h 0 k * h 3 l + h 1 k * h 2 l + h 2 k * h 1 l + h 3 k * h 0 l
  linear_combination (Rh - 2 * β - w) * hg - (2 * α + u) * hh +
    (u * w + 2 * α * β + α * w + u * β) * h2

theorem minorMap_mul [CharP K 2] {g h : Matrix (Fin 4) (Fin 4) K}
    (hg : g * minorJ K * gᵀ = minorJ K) (hh : hᵀ * minorJ K * h = minorJ K) :
    minorMap (g * h) = minorMap g * minorMap h := by
  ext A B
  have hg' := congrFun (congrFun hg (minorIdx A).1) (minorIdx A).2
  rw [mul_minorJ_mul_transpose_apply, minorJ_minorIdx] at hg'
  have hh' := congrFun (congrFun hh (minorIdx B).1) (minorIdx B).2
  rw [transpose_mul_minorJ_mul_apply, minorJ_minorIdx] at hh'
  rw [minorMap_apply, minor_mul_aux g h _ _ _ _ hg' hh', mul_apply, Fin.sum_univ_four]
  simp only [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]
  ring

theorem minorMap_one : minorMap (1 : Matrix (Fin 4) (Fin 4) K) = 1 :=
  CFSG.LinearAlgebra.exteriorSquareMinor_one

variable (K) in
abbrev minorForm : LinearMap.BilinForm K (Fin 4 → K) := Matrix.toBilin' (minorJ K)

theorem minorForm_apply (x y : Fin 4 → K) :
    minorForm K x y = x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0 := by
  simp [Matrix.toBilin'_apply, Fin.sum_univ_four, minorJ_apply]

theorem minorForm_isAlt [CharP K 2] : (minorForm K).IsAlt := fun x => by
  rw [minorForm_apply]
  linear_combination (x 0 * x 3 + x 1 * x 2) * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem det_minorJ_ne_zero : (minorJ K).det ≠ 0 := by
  have h := congrArg Matrix.det (minorJ_mul_self (K := K))
  rw [det_mul, det_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem minorForm_nondegenerate : (minorForm K).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr det_minorJ_ne_zero

theorem mem_antiSp_iff_toLin (g : GL (Fin 4) K) :
    g ∈ antiSp K ↔ GeneralLinearGroup.toLin g ∈
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (minorForm K) := by
  rw [mem_antiSp, CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup]
  simp only [GeneralLinearGroup.coe_toLin, mulVecLin_apply]
  have key : ∀ x y, minorForm K (glMat g *ᵥ x) (glMat g *ᵥ y) =
      Matrix.toBilin' ((glMat g)ᵀ * minorJ K * glMat g) x y := by
    intro x y
    rw [← Matrix.toBilin'_comp]
    rfl
  constructor
  · intro h x y
    rw [key, h]
  · intro h
    apply Matrix.toBilin'.injective
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [← key]
    exact h x y

theorem antiSp_eq_closure [CharP K 2] :
    antiSp K = Subgroup.closure {g | ∃ (v : Fin 4 → K) (t : K),
      g = GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
        (minorForm K) minorForm_isAlt v t)} := by
  have h1 : antiSp K = (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
      (minorForm K)).comap GeneralLinearGroup.toLin.toMonoidHom := by
    ext g
    exact mem_antiSp_iff_toLin g
  have key : ∀ H : Subgroup (LinearMap.GeneralLinearGroup K (Fin 4 → K)),
      H.comap (GeneralLinearGroup.toLin (n := Fin 4) (R := K)).toMonoidHom =
        H.map (GeneralLinearGroup.toLin (n := Fin 4) (R := K)).symm.toMonoidHom :=
    fun H => Subgroup.comap_equiv_eq_map_symm GeneralLinearGroup.toLin H
  rw [h1, CFSG.ClassicalGroups.Alternating.alternating_transvection_generation minorForm_isAlt
    minorForm_nondegenerate, key, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨v, t, rfl⟩, rfl⟩
    exact ⟨v, t, rfl⟩
  · rintro ⟨v, t, rfl⟩
    exact ⟨_, ⟨v, t, rfl⟩, rfl⟩

@[expose] def transvMat (v : Fin 4 → K) (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 + t * v 0 * v 3, t * v 0 * v 2, t * v 0 * v 1, t * v 0 * v 0;
    t * v 1 * v 3, 1 + t * v 1 * v 2, t * v 1 * v 1, t * v 1 * v 0;
    t * v 2 * v 3, t * v 2 * v 2, 1 + t * v 2 * v 1, t * v 2 * v 0;
    t * v 3 * v 3, t * v 3 * v 2, t * v 3 * v 1, 1 + t * v 3 * v 0]

@[expose] def transvImageMat (v : Fin 4 → K) (t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 + t * (v 1 * v 2 + v 0 * v 3), t * v 1 ^ 2, t * v 0 ^ 2, 0;
    t * v 2 ^ 2, 1 + t * (v 1 * v 2 + v 0 * v 3), 0, t * v 0 ^ 2;
    t * v 3 ^ 2, 0, 1 + t * (v 1 * v 2 + v 0 * v 3), t * v 1 ^ 2;
    0, t * v 3 ^ 2, t * v 2 ^ 2, 1 + t * (v 1 * v 2 + v 0 * v 3)]

theorem glMat_transvection [CharP K 2] (v : Fin 4 → K) (t : K) :
    glMat (GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
      (minorForm K) minorForm_isAlt v t)) = transvMat v t := by
  set g := GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
    (minorForm K) minorForm_isAlt v t) with hgdef
  have hg : ∀ x, glMat g *ᵥ x = x + (t * minorForm K x v) • v := by
    intro x
    have h1 : GeneralLinearGroup.toLin g = CFSG.ClassicalGroups.Alternating.symplecticTransvection
        (minorForm K) minorForm_isAlt v t := MulEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun f : LinearMap.GeneralLinearGroup K (Fin 4 → K) =>
      (f : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x) h1
    simp only [GeneralLinearGroup.coe_toLin, mulVecLin_apply,
      CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply] at h2
    exact h2
  ext i j
  have h3 := congrFun (hg (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h3
  rw [h3]
  fin_cases i <;> fin_cases j <;> simp [transvMat, minorForm_apply] <;> ring

theorem minorMap_transvMat [CharP K 2] (v : Fin 4 → K) (t : K) :
    minorMap (transvMat v t) = transvImageMat v t := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext A B
  fin_cases A <;> fin_cases B <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one,
    minorIdx_two, minorIdx_three, transvMat, transvImageMat]
  all_goals first
    | ring1
    | linear_combination ((v 3)^2*t) * h2
    | linear_combination ((v 0)^2*t) * h2
    | linear_combination (-(v 3)^2*t) * h2
    | linear_combination (-(v 0)^2*t) * h2

theorem transvImageMat_mem [CharP K 2] (v : Fin 4 → K) (t : K) :
    (transvImageMat v t)ᵀ * minorJ K * transvImageMat v t = minorJ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvImageMat, mul_apply, Fin.sum_univ_four, minorJ_apply]
  all_goals first
    | ring1
    | linear_combination ((v 0)^2*(v 2)^2*t^2) * h2
    | linear_combination ((v 2)^2*(v 3)^2*t^2) * h2
    | linear_combination ((v 0)^2*(v 1)^2*t^2) * h2
    | linear_combination ((v 1)^2*(v 3)^2*t^2) * h2
    | linear_combination (-(v 1)^2*(v 3)^2*t^2) * h2
    | linear_combination (-(v 0)^2*(v 2)^2*t^2) * h2
    | linear_combination (-(v 2)^2*(v 3)^2*t^2) * h2
    | linear_combination (-(v 0)^2*(v 1)^2*t^2) * h2
    | linear_combination ((v 0)*(v 1)^2*(v 3)*t^2 + (v 1)^3*(v 2)*t^2 + (v 1)^2*t) * h2
    | linear_combination ((v 0)*(v 3)^3*t^2 + (v 1)*(v 2)*(v 3)^2*t^2 + (v 3)^2*t) * h2
    | linear_combination ((v 0)*(v 2)^2*(v 3)*t^2 + (v 1)*(v 2)^3*t^2 + (v 2)^2*t) * h2
    | linear_combination ((v 0)^3*(v 3)*t^2 + (v 0)^2*(v 1)*(v 2)*t^2 + (v 0)^2*t) * h2
    | linear_combination (-(v 0)*(v 3)^3*t^2 - (v 1)*(v 2)*(v 3)^2*t^2 - (v 3)^2*t) * h2
    | linear_combination (-(v 0)*(v 1)^2*(v 3)*t^2 - (v 1)^3*(v 2)*t^2 - (v 1)^2*t) * h2
    | linear_combination (-(v 0)*(v 2)^2*(v 3)*t^2 - (v 1)*(v 2)^3*t^2 - (v 2)^2*t) * h2
    | linear_combination (-(v 0)^3*(v 3)*t^2 - (v 0)^2*(v 1)*(v 2)*t^2 - (v 0)^2*t) * h2
    | linear_combination ((v 0)^2*(v 3)^2*t^2 + (v 0)*(v 1)*(v 2)*(v 3)*t^2 + (v 0)*(v 3)*t +
        (v 1)^2*(v 2)^2*t^2 + (v 1)*(v 2)*t) * h2

theorem minorMap_transvImageMat [CharP K 2] (v : Fin 4 → K) (t : K) :
    minorMap (transvImageMat v t) = transvMat (fun i => v i ^ 2) (t ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext A B
  fin_cases A <;> fin_cases B <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one,
    minorIdx_two, minorIdx_three, transvMat, transvImageMat]
  all_goals first
    | ring1
    | linear_combination ((v 0)^2*(v 2)^2*t^2) * h2
    | linear_combination ((v 1)^2*(v 3)^2*t^2) * h2
    | linear_combination (-(v 1)^2*(v 3)^2*t^2) * h2
    | linear_combination (-(v 0)^2*(v 2)^2*t^2) * h2
    | linear_combination ((v 0)*(v 1)*(v 2)*(v 3)*t^2 + (v 0)*(v 3)*t + (v 1)*(v 2)*t) * h2

theorem transvMat_map_sq [CharP K 2] (v : Fin 4 → K) (t : K) :
    (transvMat v t).map (fun x => x ^ 2) = transvMat (fun i => v i ^ 2) (t ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat]
  all_goals first
    | ring1
    | linear_combination ((v 1)*(v 2)*t) * h2
    | linear_combination ((v 0)*(v 3)*t) * h2

theorem transpose_mul_minorJ_mul_of_mul_eq_one {M N : Matrix (Fin 4) (Fin 4) K}
    (hM : Mᵀ * minorJ K * M = minorJ K) (hNM : N * M = 1) : Nᵀ * minorJ K * N = minorJ K := by
  have hMN : M * N = 1 := mul_eq_one_comm.mp hNM
  calc Nᵀ * minorJ K * N = Nᵀ * (Mᵀ * minorJ K * M) * N := by rw [hM]
    _ = (M * N)ᵀ * minorJ K * (M * N) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = minorJ K := by rw [hMN, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem minorMap_mem [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K) :
    (minorMap (glMat g))ᵀ * minorJ K * minorMap (glMat g) = minorJ K := by
  have hS := antiSp_eq_closure (K := K)
  rw [hS] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, t, rfl⟩ := hx
    rw [glMat_transvection, minorMap_transvMat]
    exact transvImageMat_mem v t
  | one =>
    rw [show glMat (1 : GL (Fin 4) K) = 1 from rfl, minorMap_one, transpose_one, Matrix.one_mul,
      Matrix.mul_one]
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ antiSp K := hS ▸ hx
    have hy' : y ∈ antiSp K := hS ▸ hy
    rw [show glMat (x * y) = glMat x * glMat y from rfl,
      minorMap_mul (mul_minorJ_mul_transpose_of_mem hx') (mem_antiSp.mp hy')]
    calc (minorMap (glMat x) * minorMap (glMat y))ᵀ * minorJ K *
          (minorMap (glMat x) * minorMap (glMat y))
        _ = (minorMap (glMat y))ᵀ * ((minorMap (glMat x))ᵀ * minorJ K * minorMap (glMat x)) *
            minorMap (glMat y) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = minorJ K := by rw [ihx, ihy]
  | inv x hx ihx =>
    have hx' : x ∈ antiSp K := hS ▸ hx
    have h1 : minorMap (glMat x⁻¹) * minorMap (glMat x) = 1 := by
      rw [← minorMap_mul (mul_minorJ_mul_transpose_of_mem (inv_mem hx')) (mem_antiSp.mp hx'),
        show glMat x⁻¹ * glMat x = 1 from x.inv_mul, minorMap_one]
    exact transpose_mul_minorJ_mul_of_mul_eq_one ihx h1

theorem minorMap_mul_minorMap_inv [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K) :
    minorMap (glMat g) * minorMap (glMat g⁻¹) = 1 := by
  rw [← minorMap_mul (mul_minorJ_mul_transpose_of_mem hg) (mem_antiSp.mp (inv_mem hg)),
    show glMat g * glMat g⁻¹ = 1 from g.mul_inv, minorMap_one]

theorem minorMap_inv_mul_minorMap [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K) :
    minorMap (glMat g⁻¹) * minorMap (glMat g) = 1 := by
  rw [← minorMap_mul (mul_minorJ_mul_transpose_of_mem (inv_mem hg)) (mem_antiSp.mp hg),
    show glMat g⁻¹ * glMat g = 1 from g.inv_mul, minorMap_one]

variable (K) in
@[expose] def minorHom [CharP K 2] : antiSp K →* antiSp K where
  toFun g := ⟨⟨minorMap (glMat g), minorMap (glMat (g : GL (Fin 4) K)⁻¹),
    minorMap_mul_minorMap_inv g.2, minorMap_inv_mul_minorMap g.2⟩, minorMap_mem g.2⟩
  map_one' := Subtype.ext (Units.ext minorMap_one)
  map_mul' g h := Subtype.ext (Units.ext
    (minorMap_mul (mul_minorJ_mul_transpose_of_mem g.2) (mem_antiSp.mp h.2)))

theorem glMat_minorHom [CharP K 2] (g : antiSp K) :
    glMat (minorHom K g : GL (Fin 4) K) = minorMap (glMat g) :=
  rfl

theorem minorJ_map {L : Type} [Field L] (f : K →+* L) : (minorJ K).map f = minorJ L := by
  ext i j
  rw [Matrix.map_apply, minorJ_apply, minorJ_apply]
  split_ifs <;> simp

variable (K) in
@[expose] def frobHom [CharP K 2] : antiSp K →* antiSp K :=
  ((GeneralLinearGroup.map (frobenius K 2)).comp (antiSp K).subtype).codRestrict (antiSp K)
    fun g => by
      rw [mem_antiSp]
      change ((glMat g).map (frobenius K 2))ᵀ * minorJ K * (glMat g).map (frobenius K 2) =
        minorJ K
      rw [← minorJ_map (frobenius K 2), ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        mem_antiSp.mp g.2]

theorem glMat_frobHom [CharP K 2] (g : antiSp K) :
    glMat (frobHom K g : GL (Fin 4) K) = (glMat g).map fun x => x ^ 2 := by
  ext i j
  exact frobenius_def 2 _

theorem minorHom_minorHom [CharP K 2] (g : antiSp K) :
    minorHom K (minorHom K g) = frobHom K g := by
  have hS := antiSp_eq_closure (K := K)
  have key : ∀ x (hx : x ∈ Subgroup.closure {g | ∃ (v : Fin 4 → K) (t : K),
      g = GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
        (minorForm K) minorForm_isAlt v t)}), ∀ hx' : x ∈ antiSp K,
      minorHom K (minorHom K ⟨x, hx'⟩) = frobHom K ⟨x, hx'⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hx'
      obtain ⟨v, t, rfl⟩ := hx
      refine Subtype.ext (Units.ext ?_)
      change glMat (minorHom K (minorHom K _) : GL (Fin 4) K) = glMat (frobHom K _ : GL (Fin 4) K)
      rw [glMat_minorHom, glMat_minorHom, glMat_frobHom]
      rw [glMat_transvection, minorMap_transvMat, minorMap_transvImageMat, transvMat_map_sq]
    | one =>
      intro h1
      rw [show (⟨1, h1⟩ : antiSp K) = 1 from rfl, map_one, map_one, map_one]
    | mul x y hx hy ihx ihy =>
      intro hxy
      have hx' : x ∈ antiSp K := hS ▸ hx
      have hy' : y ∈ antiSp K := hS ▸ hy
      rw [show (⟨x * y, hxy⟩ : antiSp K) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from rfl, map_mul, map_mul,
        map_mul, ihx hx', ihy hy']
    | inv x hx ihx =>
      intro hxi
      have hx' : x ∈ antiSp K := hS ▸ hx
      rw [show (⟨x⁻¹, hxi⟩ : antiSp K) = (⟨x, hx'⟩ : antiSp K)⁻¹ from rfl, map_inv, map_inv,
        map_inv, ihx hx']
  exact key g.1 (hS ▸ g.2) g.2

theorem minorHom_bijective [CharP K 2] [Finite K] : Function.Bijective (minorHom K) := by
  have hFinj : Function.Injective (frobHom K) := by
    intro g h hgh
    have h1 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hgh
    simp only [glMat_frobHom] at h1
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.map_apply] at h2
    exact (frobenius_inj K 2) ((frobenius_def 2 _).trans (h2.trans (frobenius_def 2 _).symm))
  have hinj : Function.Injective (minorHom K) := by
    intro g h hgh
    apply hFinj
    rw [← minorHom_minorHom, ← minorHom_minorHom, hgh]
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

variable (K) in
@[expose] def minorAut [CharP K 2] [Finite K] : MulAut (antiSp K) :=
  MulEquiv.ofBijective (minorHom K) minorHom_bijective

theorem glMat_minorAut [CharP K 2] [Finite K] (g : antiSp K) :
    glMat (minorAut K g : GL (Fin 4) K) = minorMap (glMat g) :=
  rfl

end Mul

end SpChain

end CFSG.ComponentClassification.UnbalancedCatalog
