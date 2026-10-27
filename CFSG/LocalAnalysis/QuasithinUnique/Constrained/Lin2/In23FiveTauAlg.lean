module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.QuasithinUnique.Lin2.Five

open Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

section TauAlg

variable {R : Type*} [CommRing R]

@[expose] def jm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R := Matrix.fromBlocks 0 1 (-1) 0

@[expose] def tauPair : Fin 2 ⊕ Fin 2 → (Fin 2 ⊕ Fin 2) × (Fin 2 ⊕ Fin 2) :=
  Sum.elim ![(ι₀, ι₁), (ι₀, ι₃)] ![(ι₂, ι₃), (ι₁, ι₂)]

@[expose] def tauMat (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.of fun r c => g (tauPair r).1 (tauPair c).1 * g (tauPair r).2 (tauPair c).2 -
    g (tauPair r).1 (tauPair c).2 * g (tauPair r).2 (tauPair c).1

theorem tauMat_apply (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) (r c : Fin 2 ⊕ Fin 2) :
    tauMat g r c = g (tauPair r).1 (tauPair c).1 * g (tauPair r).2 (tauPair c).2 -
      g (tauPair r).1 (tauPair c).2 * g (tauPair r).2 (tauPair c).1 := rfl

theorem tauPair_ι₀ : tauPair ι₀ = (ι₀, ι₁) := rfl
theorem tauPair_ι₁ : tauPair ι₁ = (ι₀, ι₃) := rfl
theorem tauPair_ι₂ : tauPair ι₂ = (ι₂, ι₃) := rfl
theorem tauPair_ι₃ : tauPair ι₃ = (ι₁, ι₂) := rfl

omit [CommRing R] in
theorem matrix_ext16 {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (h00 : M ι₀ ι₀ = N ι₀ ι₀) (h01 : M ι₀ ι₁ = N ι₀ ι₁) (h02 : M ι₀ ι₂ = N ι₀ ι₂)
    (h03 : M ι₀ ι₃ = N ι₀ ι₃) (h10 : M ι₁ ι₀ = N ι₁ ι₀) (h11 : M ι₁ ι₁ = N ι₁ ι₁)
    (h12 : M ι₁ ι₂ = N ι₁ ι₂) (h13 : M ι₁ ι₃ = N ι₁ ι₃) (h20 : M ι₂ ι₀ = N ι₂ ι₀)
    (h21 : M ι₂ ι₁ = N ι₂ ι₁) (h22 : M ι₂ ι₂ = N ι₂ ι₂) (h23 : M ι₂ ι₃ = N ι₂ ι₃)
    (h30 : M ι₃ ι₀ = N ι₃ ι₀) (h31 : M ι₃ ι₁ = N ι₃ ι₁) (h32 : M ι₃ ι₂ = N ι₃ ι₂)
    (h33 : M ι₃ ι₃ = N ι₃ ι₃) : M = N := by
  ext r c
  fin_cases r <;> fin_cases c <;> assumption

theorem tauMat_one : tauMat (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [tauMat, tauPair, Matrix.one_apply]



structure Sc (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) : Prop where
  c01 : -(g ι₁ ι₁)*(g ι₃ ι₀) + (g ι₁ ι₀)*(g ι₃ ι₁) - (g ι₀ ι₁)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₁) = 0
  r01 : -(g ι₀ ι₃)*(g ι₁ ι₁) - (g ι₀ ι₂)*(g ι₁ ι₀) + (g ι₀ ι₁)*(g ι₁ ι₃) + (g ι₀ ι₀)*(g ι₁ ι₂) = 0
  c02 : -(g ι₁ ι₂)*(g ι₃ ι₀) + (g ι₁ ι₀)*(g ι₃ ι₂) - (g ι₀ ι₂)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₂) = 1
  r02 : -(g ι₀ ι₃)*(g ι₂ ι₁) - (g ι₀ ι₂)*(g ι₂ ι₀) + (g ι₀ ι₁)*(g ι₂ ι₃) + (g ι₀ ι₀)*(g ι₂ ι₂) = 1
  c03 : -(g ι₁ ι₃)*(g ι₃ ι₀) + (g ι₁ ι₀)*(g ι₃ ι₃) - (g ι₀ ι₃)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₃) = 0
  r03 : -(g ι₀ ι₃)*(g ι₃ ι₁) - (g ι₀ ι₂)*(g ι₃ ι₀) + (g ι₀ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₀)*(g ι₃ ι₂) = 0
  c12 : -(g ι₁ ι₂)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₃ ι₂) - (g ι₀ ι₂)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₂) = 0
  r12 : -(g ι₁ ι₃)*(g ι₂ ι₁) - (g ι₁ ι₂)*(g ι₂ ι₀) + (g ι₁ ι₁)*(g ι₂ ι₃) + (g ι₁ ι₀)*(g ι₂ ι₂) = 0
  c13 : -(g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₃ ι₃) - (g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₃) = 1
  r13 : -(g ι₁ ι₃)*(g ι₃ ι₁) - (g ι₁ ι₂)*(g ι₃ ι₀) + (g ι₁ ι₁)*(g ι₃ ι₃) + (g ι₁ ι₀)*(g ι₃ ι₂) = 1
  c23 : -(g ι₁ ι₃)*(g ι₃ ι₂) + (g ι₁ ι₂)*(g ι₃ ι₃) - (g ι₀ ι₃)*(g ι₂ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₃) = 0
  r23 : -(g ι₂ ι₃)*(g ι₃ ι₁) - (g ι₂ ι₂)*(g ι₃ ι₀) + (g ι₂ ι₁)*(g ι₃ ι₃) + (g ι₂ ι₀)*(g ι₃ ι₂) = 0

theorem Sc.of_matrix {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hc : gᵀ * jm * g = jm) (hr : g * jm * gᵀ = jm) : Sc g where
  c01 := by
    have h := congrFun (congrFun hc ι₀) ι₁
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  r01 := by
    have h := congrFun (congrFun hr ι₀) ι₁
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  c02 := by
    have h := congrFun (congrFun hc ι₀) ι₂
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  r02 := by
    have h := congrFun (congrFun hr ι₀) ι₂
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  c03 := by
    have h := congrFun (congrFun hc ι₀) ι₃
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  r03 := by
    have h := congrFun (congrFun hr ι₀) ι₃
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  c12 := by
    have h := congrFun (congrFun hc ι₁) ι₂
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  r12 := by
    have h := congrFun (congrFun hr ι₁) ι₂
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  c13 := by
    have h := congrFun (congrFun hc ι₁) ι₃
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  r13 := by
    have h := congrFun (congrFun hr ι₁) ι₃
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  c23 := by
    have h := congrFun (congrFun hc ι₂) ι₃
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h
  r23 := by
    have h := congrFun (congrFun hr ι₂) ι₃
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm] at h
    linear_combination h

theorem Sc.to_col {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    gᵀ * jm * g = jm := by
  apply matrix_ext16
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.c01
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.c02
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.c03
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.c01
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.c12
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.c13
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.c02
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.c12
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.c23
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.c03
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.c13
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.c23
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring

theorem Sc.to_row {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    g * jm * gᵀ = jm := by
  apply matrix_ext16
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.r01
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.r02
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.r03
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.r01
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.r12
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.r13
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.r02
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.r12
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination hg.r23
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.r03
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.r13
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    linear_combination (-1 : R) * hg.r23
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, jm]
    ring

theorem tauMul_00 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₀ ι₀ = (tauMat g * tauMat h) ι₀ ι₀ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * hh.c01 + ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * hg.r01 - ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * h2

theorem tauMul_01 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₀ ι₁ = (tauMat g * tauMat h) ι₀ ι₁ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * hh.c03 + ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * hg.r01 - ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * h2

theorem tauMul_02 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₀ ι₂ = (tauMat g * tauMat h) ι₀ ι₂ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * hh.c23 + ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * hg.r01 - ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * h2

theorem tauMul_03 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₀ ι₃ = (tauMat g * tauMat h) ι₀ ι₃ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * hh.c12 + ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * hg.r01 - ((g ι₀ ι₀) * (g ι₁ ι₂) - (g ι₀ ι₂) * (g ι₁ ι₀)) * ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * h2

theorem tauMul_10 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₁ ι₀ = (tauMat g * tauMat h) ι₁ ι₀ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * hh.c01 + ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * hg.r03 - ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * h2

theorem tauMul_11 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₁ ι₁ = (tauMat g * tauMat h) ι₁ ι₁ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * hh.c03 + ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * hg.r03 - ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * h2

theorem tauMul_12 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₁ ι₂ = (tauMat g * tauMat h) ι₁ ι₂ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * hh.c23 + ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * hg.r03 - ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * h2

theorem tauMul_13 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₁ ι₃ = (tauMat g * tauMat h) ι₁ ι₃ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * hh.c12 + ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * hg.r03 - ((g ι₀ ι₀) * (g ι₃ ι₂) - (g ι₀ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * h2

theorem tauMul_20 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₂ ι₀ = (tauMat g * tauMat h) ι₂ ι₀ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * hh.c01 + ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * hg.r23 - ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * h2

theorem tauMul_21 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₂ ι₁ = (tauMat g * tauMat h) ι₂ ι₁ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * hh.c03 + ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * hg.r23 - ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * h2

theorem tauMul_22 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₂ ι₂ = (tauMat g * tauMat h) ι₂ ι₂ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * hh.c23 + ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * hg.r23 - ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * h2

theorem tauMul_23 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₂ ι₃ = (tauMat g * tauMat h) ι₂ ι₃ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * hh.c12 + ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * hg.r23 - ((g ι₂ ι₀) * (g ι₃ ι₂) - (g ι₂ ι₂) * (g ι₃ ι₀)) * ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * h2

theorem tauMul_30 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₃ ι₀ = (tauMat g * tauMat h) ι₃ ι₀ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * hh.c01 + ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * hg.r12 - ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₁) - (h ι₁ ι₁) * (h ι₃ ι₀)) * h2

theorem tauMul_31 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₃ ι₁ = (tauMat g * tauMat h) ι₃ ι₁ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * hh.c03 + ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * hg.r12 - ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * ((h ι₁ ι₀) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₀)) * h2

theorem tauMul_32 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₃ ι₂ = (tauMat g * tauMat h) ι₃ ι₂ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * hh.c23 + ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * hg.r12 - ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * ((h ι₁ ι₂) * (h ι₃ ι₃) - (h ι₁ ι₃) * (h ι₃ ι₂)) * h2

theorem tauMul_33 (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) :
    tauMat (g * h) ι₃ ι₃ = (tauMat g * tauMat h) ι₃ ι₃ := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  linear_combination ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * hh.c12 + ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * hg.r12 - ((g ι₁ ι₀) * (g ι₂ ι₂) - (g ι₁ ι₂) * (g ι₂ ι₀)) * ((h ι₁ ι₁) * (h ι₃ ι₂) - (h ι₁ ι₂) * (h ι₃ ι₁)) * h2

theorem tauMat_mul (h2 : (2 : R) = 0) {g h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) (hh : Sc h) : tauMat (g * h) = tauMat g * tauMat h :=
  matrix_ext16 (tauMul_00 h2 hg hh) (tauMul_01 h2 hg hh) (tauMul_02 h2 hg hh) (tauMul_03 h2 hg hh) (tauMul_10 h2 hg hh) (tauMul_11 h2 hg hh) (tauMul_12 h2 hg hh) (tauMul_13 h2 hg hh) (tauMul_20 h2 hg hh) (tauMul_21 h2 hg hh) (tauMul_22 h2 hg hh) (tauMul_23 h2 hg hh) (tauMul_30 h2 hg hh) (tauMul_31 h2 hg hh) (tauMul_32 h2 hg hh) (tauMul_33 h2 hg hh)

theorem tauMat_sc (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    Sc (tauMat g) where
  c01 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₀ ι₃)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₃)) * hg.c01 + ((g ι₀ ι₁)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₁)) * hg.c03 + ((g ι₀ ι₁)*(g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₂ ι₀)*(g ι₃ ι₃) + (g ι₀ ι₁)*(g ι₀ ι₃)*(g ι₂ ι₀)^2 + (g ι₀ ι₀)*(g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₀) - (g ι₀ ι₀)*(g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₁) + (g ι₀ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₀)*(g ι₃ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₃) - (g ι₀ ι₀)^2*(g ι₂ ι₁)*(g ι₂ ι₃)) * h2
  r01 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₀ ι₂)*(g ι₀ ι₃)) * hg.c01 + ((g ι₀ ι₀)*(g ι₃ ι₂)) * hg.r01 + ((g ι₀ ι₀)*(g ι₀ ι₂)) * hg.c02 + ((g ι₀ ι₀)*(g ι₀ ι₂)) * hg.r02 + ((g ι₀ ι₁)*(g ι₀ ι₂)) * hg.c03 + ((g ι₀ ι₀)*(g ι₁ ι₂)) * hg.r03 + ((g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₁ ι₀)*(g ι₃ ι₃) + (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₃ ι₁) + (g ι₀ ι₀)*(g ι₀ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₃ ι₀) + (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₁ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₀)*(g ι₀ ι₂)^2*(g ι₂ ι₀) - (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₁ ι₂)*(g ι₃ ι₃) - (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₂ ι₃) - (g ι₀ ι₀)^2*(g ι₁ ι₂)*(g ι₃ ι₂) - (g ι₀ ι₀)^2*(g ι₀ ι₂)*(g ι₂ ι₂)) * h2
  c02 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₃)) * hg.c02 + (1) * hg.r02 + ((g ι₀ ι₂)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₂)) * hg.c03 + ((g ι₀ ι₃)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₃)) * hg.c12 + ((g ι₀ ι₂)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₂)) * hg.c13 + ((g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₁) - (g ι₀ ι₃)*(g ι₁ ι₁)*(g ι₂ ι₀)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₀) + (g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₀) - (g ι₀ ι₂)*(g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₃) + 2*(g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₁ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₁) - (g ι₀ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₂) - 2*(g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₂ ι₂)*(g ι₂ ι₃)) * h2
  r02 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₀ ι₃)*(g ι₂ ι₂)) * hg.c01 + ((g ι₂ ι₂)*(g ι₃ ι₀)) * hg.r01 + ((g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₃) + (g ι₀ ι₀)*(g ι₂ ι₂)) * hg.c02 + (1 + (g ι₀ ι₀)*(g ι₂ ι₂)) * hg.r02 + ((g ι₀ ι₁)*(g ι₂ ι₂)) * hg.c03 + ((g ι₁ ι₂)*(g ι₂ ι₀)) * hg.r03 + ((g ι₀ ι₂)*(g ι₃ ι₀) + (g ι₀ ι₀)*(g ι₃ ι₂)) * hg.r12 + ((g ι₀ ι₂)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₂)) * hg.c13 + ((g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₁) + (g ι₀ ι₃)*(g ι₁ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₀) - (g ι₀ ι₃)*(g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₀) + (g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₀) + (g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₀) - (g ι₀ ι₂)*(g ι₁ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₀) + (g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₃) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₁)*(g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₂) + (g ι₀ ι₀)*(g ι₂ ι₂) + (g ι₀ ι₀)*(g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₁ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₂) + (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₂) - 2*(g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₂ ι₂)*(g ι₂ ι₃) - (g ι₀ ι₀)^2*(g ι₂ ι₂)^2) * h2
  c03 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₀ ι₂)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₂)) * hg.c01 + ((g ι₀ ι₁)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₁)) * hg.c12 + ((g ι₀ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₂) + (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₁) - (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₂ ι₁)*(g ι₂ ι₂)) * h2
  r03 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₁ ι₂)*(g ι₂ ι₀) + (g ι₁ ι₀)*(g ι₂ ι₂)) * hg.r01 + ((g ι₀ ι₂)*(g ι₁ ι₀) + (g ι₀ ι₀)*(g ι₁ ι₂)) * hg.r12 + ((g ι₀ ι₃)*(g ι₁ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₂)) * h2
  c12 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₂ ι₃)*(g ι₃ ι₃)) * hg.r01 + ((g ι₀ ι₃)*(g ι₂ ι₃)) * hg.r02 + ((g ι₀ ι₃)*(g ι₂ ι₂)) * hg.c03 + ((g ι₁ ι₃)*(g ι₂ ι₃)) * hg.r03 + ((g ι₀ ι₃)*(g ι₂ ι₃)) * hg.c13 + ((g ι₀ ι₃)*(g ι₂ ι₀)) * hg.c23 + ((g ι₀ ι₃)*(g ι₂ ι₃) + (g ι₀ ι₃)*(g ι₁ ι₃)*(g ι₂ ι₃)*(g ι₃ ι₁) + (g ι₀ ι₃)*(g ι₁ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₀) - (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₀) + (g ι₀ ι₃)*(g ι₁ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₂) - (g ι₀ ι₃)*(g ι₁ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₃)^2*(g ι₂ ι₁)*(g ι₂ ι₃) + (g ι₀ ι₃)^2*(g ι₂ ι₀)*(g ι₂ ι₂) + (g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₂ ι₃)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₃)*(g ι₂ ι₃)*(g ι₃ ι₃) - (g ι₀ ι₁)*(g ι₀ ι₃)*(g ι₂ ι₃)^2 - (g ι₀ ι₀)*(g ι₁ ι₃)*(g ι₂ ι₃)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₃)*(g ι₂ ι₂)*(g ι₂ ι₃)) * h2
  r12 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₃ ι₂)*(g ι₃ ι₃)) * hg.c01 + ((g ι₃ ι₁)*(g ι₃ ι₂)) * hg.c03 + ((g ι₃ ι₀)*(g ι₃ ι₃)) * hg.c12 + ((g ι₃ ι₀)*(g ι₃ ι₁)) * hg.c23 + ((g ι₁ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₁)*(g ι₃ ι₂) - (g ι₁ ι₀)*(g ι₃ ι₁)*(g ι₃ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₀)*(g ι₃ ι₁) - (g ι₀ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₀)*(g ι₃ ι₂) + (g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₁)*(g ι₃ ι₂) - (g ι₀ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₁) + (g ι₀ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₀)*(g ι₃ ι₃) + (g ι₀ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₂) - (g ι₀ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₀)*(g ι₃ ι₃) - (g ι₀ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₁)*(g ι₃ ι₂)) * h2
  c13 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₁ ι₃)*(g ι₃ ι₂) + (g ι₁ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₃)) * hg.c01 + ((g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₃)) * hg.c02 + ((g ι₁ ι₂)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₃ ι₂)) * hg.c03 + ((g ι₀ ι₃)*(g ι₂ ι₀) + (g ι₀ ι₀)*(g ι₂ ι₃)) * hg.c12 + (1) * hg.c13 + ((g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₁ ι₂)*(g ι₁ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₁ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₂) + (g ι₁ ι₁)*(g ι₁ ι₂)*(g ι₃ ι₀)*(g ι₃ ι₃) - (g ι₁ ι₀)*(g ι₁ ι₃)*(g ι₃ ι₁)*(g ι₃ ι₂) - (g ι₁ ι₀)*(g ι₁ ι₂)*(g ι₃ ι₁)*(g ι₃ ι₃) - (g ι₁ ι₀)*(g ι₁ ι₁)*(g ι₃ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₀) + (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₁) - (g ι₀ ι₃)*(g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₁ ι₁)*(g ι₂ ι₀)*(g ι₃ ι₃) + (g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₂) + (g ι₀ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₂) + (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₁) - (g ι₀ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₃)*(g ι₂ ι₁)*(g ι₂ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₂ ι₂)*(g ι₂ ι₃)) * h2
  r13 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₁ ι₃)*(g ι₃ ι₂) + (g ι₁ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₂)*(g ι₂ ι₃)) * hg.c01 + ((g ι₂ ι₂)*(g ι₃ ι₀)) * hg.r01 + ((g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₂ ι₃) + (g ι₀ ι₀)*(g ι₂ ι₂)) * hg.c02 + ((g ι₀ ι₀)*(g ι₂ ι₂)) * hg.r02 + ((g ι₁ ι₂)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₁)) * hg.c03 + ((g ι₁ ι₂)*(g ι₂ ι₀)) * hg.r03 + ((g ι₀ ι₂)*(g ι₃ ι₀) + (g ι₀ ι₀)*(g ι₃ ι₂)) * hg.r12 + (1) * hg.c13 + ((g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₁ ι₂)*(g ι₁ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₁) + (g ι₁ ι₁)*(g ι₁ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₂) + (g ι₁ ι₁)*(g ι₁ ι₂)*(g ι₃ ι₀)*(g ι₃ ι₃) - (g ι₁ ι₀)*(g ι₁ ι₃)*(g ι₃ ι₁)*(g ι₃ ι₂) - (g ι₁ ι₀)*(g ι₁ ι₂)*(g ι₃ ι₁)*(g ι₃ ι₃) - (g ι₁ ι₀)*(g ι₁ ι₁)*(g ι₃ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₀) + (g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₀) + (g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₀) + (g ι₀ ι₂)*(g ι₁ ι₁)*(g ι₂ ι₀)*(g ι₃ ι₃) - (g ι₀ ι₂)*(g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₂) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₂) + (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₃) + (g ι₀ ι₀)*(g ι₂ ι₂) - (g ι₀ ι₀)*(g ι₁ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₁) - (g ι₀ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₁ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₂ ι₁)*(g ι₂ ι₃) + (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₂ ι₂)*(g ι₂ ι₃) - (g ι₀ ι₀)^2*(g ι₂ ι₂)^2) * h2
  c23 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₂ ι₂)*(g ι₃ ι₂)) * hg.r01 + ((g ι₀ ι₂)*(g ι₂ ι₂)) * hg.c02 + ((g ι₀ ι₂)*(g ι₂ ι₂)) * hg.r02 + ((g ι₁ ι₂)*(g ι₂ ι₂)) * hg.r03 + ((g ι₀ ι₂)*(g ι₂ ι₃)) * hg.c12 + ((g ι₀ ι₂)*(g ι₂ ι₁)) * hg.c23 + ((g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₂ ι₂)*(g ι₃ ι₁) + (g ι₀ ι₂)*(g ι₂ ι₂) - (g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₂ ι₂)*(g ι₃ ι₀) - (g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₃) - (g ι₀ ι₂)*(g ι₁ ι₁)*(g ι₂ ι₃)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₁ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₂ ι₁)*(g ι₂ ι₂) + (g ι₀ ι₂)^2*(g ι₂ ι₀)*(g ι₂ ι₂) - (g ι₀ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₂)*(g ι₃ ι₃) - (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₂ ι₂)*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₂)*(g ι₂ ι₂)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₂ ι₂)^2) * h2
  r23 := by
    simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
    linear_combination ((g ι₂ ι₂)*(g ι₂ ι₃)) * hg.c01 + ((g ι₂ ι₁)*(g ι₂ ι₂)) * hg.c03 + ((g ι₂ ι₀)*(g ι₂ ι₃)) * hg.c12 + ((g ι₂ ι₀)*(g ι₂ ι₁)) * hg.c23 + ((g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₀) - (g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₁) + (g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₂) + (g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₁) - (g ι₁ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₃) - (g ι₁ ι₁)*(g ι₂ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₂) + (g ι₁ ι₁)*(g ι₂ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₃) - (g ι₁ ι₀)*(g ι₂ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁)*(g ι₂ ι₂) - (g ι₀ ι₀)*(g ι₂ ι₁)*(g ι₂ ι₂)*(g ι₂ ι₃)) * h2

theorem tauTau_00 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₀ ι₀ = g ι₀ ι₀ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁]
  linear_combination ((g ι₀ ι₀)*(g ι₀ ι₃)) * hg.c01 + ((g ι₀ ι₀)*(g ι₀ ι₁)) * hg.c03 + ((g ι₀ ι₀)^2) * hg.c13 + ((g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₁ ι₃)*(g ι₃ ι₀) - (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₃ ι₃) + (g ι₀ ι₀)*(g ι₀ ι₁)*(g ι₀ ι₃)*(g ι₂ ι₀) - (g ι₀ ι₀)^2*(g ι₀ ι₁)*(g ι₂ ι₃)) * h2

theorem tauTau_01 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₀ ι₁ = g ι₀ ι₁ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₃]
  linear_combination ((g ι₀ ι₁)*(g ι₀ ι₂)) * hg.c01 + ((g ι₀ ι₁)^2) * hg.c02 + ((g ι₀ ι₀)*(g ι₀ ι₁)) * hg.c12 + ((g ι₀ ι₁)^2*(g ι₁ ι₂)*(g ι₃ ι₀) - (g ι₀ ι₁)^2*(g ι₁ ι₀)*(g ι₃ ι₂) + (g ι₀ ι₁)^2*(g ι₀ ι₂)*(g ι₂ ι₀) - (g ι₀ ι₀)*(g ι₀ ι₁)^2*(g ι₂ ι₂)) * h2

theorem tauTau_02 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₀ ι₂ = g ι₀ ι₂ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₀ ι₂)*(g ι₃ ι₂)) * hg.r01 + ((g ι₀ ι₂)^2) * hg.c02 + ((g ι₀ ι₂)^2) * hg.r02 + ((g ι₀ ι₂)*(g ι₁ ι₂)) * hg.r03 + ((g ι₀ ι₂)^2) * hg.c13 + ((g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₁ ι₂)*(g ι₃ ι₁) + (g ι₀ ι₂)^2 + (g ι₀ ι₂)^2*(g ι₁ ι₂)*(g ι₃ ι₀) + (g ι₀ ι₂)^2*(g ι₀ ι₃)*(g ι₂ ι₁) + (g ι₀ ι₂)^3*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₃ ι₃) - (g ι₀ ι₁)*(g ι₀ ι₂)^2*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₀ ι₂)*(g ι₁ ι₂)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₂)^2*(g ι₂ ι₂)) * h2

theorem tauTau_03 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₀ ι₃ = g ι₀ ι₃ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₀ ι₃)*(g ι₃ ι₃)) * hg.r01 + ((g ι₀ ι₃)^2) * hg.c02 + ((g ι₀ ι₃)^2) * hg.r02 + ((g ι₀ ι₃)*(g ι₁ ι₃)) * hg.r03 + ((g ι₀ ι₃)^2) * hg.c13 + ((g ι₀ ι₃)^2 + (g ι₀ ι₃)^2*(g ι₁ ι₃)*(g ι₃ ι₁) + (g ι₀ ι₃)^3*(g ι₂ ι₁) + (g ι₀ ι₂)*(g ι₀ ι₃)*(g ι₁ ι₃)*(g ι₃ ι₀) + (g ι₀ ι₂)*(g ι₀ ι₃)^2*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₀ ι₃)*(g ι₁ ι₃)*(g ι₃ ι₃) - (g ι₀ ι₁)*(g ι₀ ι₃)^2*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₀ ι₃)*(g ι₁ ι₃)*(g ι₃ ι₂) - (g ι₀ ι₀)*(g ι₀ ι₃)^2*(g ι₂ ι₂)) * h2

theorem tauTau_10 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₁ ι₀ = g ι₁ ι₀ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₃]
  linear_combination ((g ι₁ ι₀)*(g ι₂ ι₀)) * hg.r01 + ((g ι₁ ι₀)^2) * hg.r02 + ((g ι₀ ι₀)*(g ι₁ ι₀)) * hg.r12 + ((g ι₀ ι₃)*(g ι₁ ι₀)^2*(g ι₂ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₀)^2*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)^2*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₀)^2*(g ι₂ ι₂)) * h2

theorem tauTau_11 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₁ ι₁ = g ι₁ ι₁ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₃]
  linear_combination ((g ι₁ ι₁)*(g ι₁ ι₂)) * hg.c01 + ((g ι₁ ι₁)^2) * hg.c02 + ((g ι₁ ι₀)*(g ι₁ ι₁)) * hg.c12 + ((g ι₁ ι₁)^2*(g ι₁ ι₂)*(g ι₃ ι₀) - (g ι₁ ι₀)*(g ι₁ ι₁)^2*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₁ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₁) + (g ι₀ ι₁)*(g ι₁ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₀)*(g ι₁ ι₁)*(g ι₂ ι₂) - (g ι₀ ι₀)*(g ι₁ ι₁)*(g ι₁ ι₂)*(g ι₂ ι₁)) * h2

theorem tauTau_12 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₁ ι₂ = g ι₁ ι₂ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₁ ι₂)*(g ι₂ ι₂)) * hg.r01 + ((g ι₁ ι₂)^2) * hg.r02 + ((g ι₀ ι₂)*(g ι₁ ι₂)) * hg.r12 + ((g ι₀ ι₃)*(g ι₁ ι₂)^2*(g ι₂ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₂)^2*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₂)^2*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₂)^2*(g ι₂ ι₂)) * h2

theorem tauTau_13 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₁ ι₃ = g ι₁ ι₃ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₁ ι₃)*(g ι₂ ι₃)) * hg.r01 + ((g ι₁ ι₃)^2) * hg.r02 + ((g ι₀ ι₃)*(g ι₁ ι₃)) * hg.r12 + ((g ι₀ ι₃)*(g ι₁ ι₃)^2*(g ι₂ ι₁) + (g ι₀ ι₂)*(g ι₁ ι₃)^2*(g ι₂ ι₀) - (g ι₀ ι₁)*(g ι₁ ι₃)^2*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₁ ι₃)^2*(g ι₂ ι₂)) * h2

theorem tauTau_20 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₂ ι₀ = g ι₂ ι₀ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₂ ι₀)*(g ι₂ ι₃)) * hg.c01 + ((g ι₂ ι₀)*(g ι₂ ι₁)) * hg.c03 + ((g ι₂ ι₀)^2) * hg.c13 + ((g ι₁ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₀) - (g ι₁ ι₀)*(g ι₂ ι₀)*(g ι₂ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₀)^2*(g ι₂ ι₁) - (g ι₀ ι₀)*(g ι₂ ι₀)*(g ι₂ ι₁)*(g ι₂ ι₃)) * h2

theorem tauTau_21 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₂ ι₁ = g ι₂ ι₁ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₂ ι₁)*(g ι₂ ι₂)) * hg.c01 + ((g ι₂ ι₁)^2) * hg.c02 + ((g ι₂ ι₀)*(g ι₂ ι₁)) * hg.c12 + ((g ι₁ ι₂)*(g ι₂ ι₁)^2*(g ι₃ ι₀) - (g ι₁ ι₀)*(g ι₂ ι₁)^2*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₂ ι₁)^2 - (g ι₀ ι₀)*(g ι₂ ι₁)^2*(g ι₂ ι₂)) * h2

theorem tauTau_22 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₂ ι₂ = g ι₂ ι₂ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₂ ι₂)*(g ι₂ ι₃)) * hg.c12 + ((g ι₂ ι₂)^2) * hg.c13 + ((g ι₂ ι₁)*(g ι₂ ι₂)) * hg.c23 + ((g ι₁ ι₃)*(g ι₂ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₂) + (g ι₁ ι₂)*(g ι₂ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₁) - (g ι₁ ι₂)*(g ι₂ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₃) - (g ι₁ ι₁)*(g ι₂ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₂) + (g ι₀ ι₃)*(g ι₂ ι₁)*(g ι₂ ι₂)^2 - (g ι₀ ι₁)*(g ι₂ ι₂)^2*(g ι₂ ι₃)) * h2

theorem tauTau_23 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₂ ι₃ = g ι₂ ι₃ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₂ ι₃)^2) * hg.c02 + ((g ι₂ ι₂)*(g ι₂ ι₃)) * hg.c03 + ((g ι₂ ι₀)*(g ι₂ ι₃)) * hg.c23 + ((g ι₁ ι₃)*(g ι₂ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₀) - (g ι₁ ι₀)*(g ι₂ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₂ ι₂)*(g ι₂ ι₃) - (g ι₀ ι₀)*(g ι₂ ι₂)*(g ι₂ ι₃)^2) * h2

theorem tauTau_30 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₃ ι₀ = g ι₃ ι₀ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₃ ι₀)*(g ι₃ ι₃)) * hg.c01 + ((g ι₃ ι₀)*(g ι₃ ι₁)) * hg.c03 + ((g ι₃ ι₀)^2) * hg.c13 + ((g ι₁ ι₃)*(g ι₃ ι₀)^2*(g ι₃ ι₁) - (g ι₁ ι₀)*(g ι₃ ι₀)*(g ι₃ ι₁)*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₀)*(g ι₃ ι₁) - (g ι₀ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₁)) * h2

theorem tauTau_31 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₃ ι₁ = g ι₃ ι₁ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₃ ι₁)*(g ι₃ ι₂)) * hg.c01 + ((g ι₃ ι₁)^2) * hg.c02 + ((g ι₃ ι₀)*(g ι₃ ι₁)) * hg.c12 + ((g ι₁ ι₂)*(g ι₃ ι₀)*(g ι₃ ι₁)^2 - (g ι₁ ι₀)*(g ι₃ ι₁)^2*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₀)*(g ι₃ ι₁)^2 - (g ι₀ ι₀)*(g ι₂ ι₂)*(g ι₃ ι₁)^2) * h2

theorem tauTau_32 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₃ ι₂ = g ι₃ ι₂ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₃ ι₂)*(g ι₃ ι₃)) * hg.c12 + ((g ι₃ ι₂)^2) * hg.c13 + ((g ι₃ ι₁)*(g ι₃ ι₂)) * hg.c23 + ((g ι₁ ι₃)*(g ι₃ ι₁)*(g ι₃ ι₂)^2 - (g ι₁ ι₁)*(g ι₃ ι₂)^2*(g ι₃ ι₃) + (g ι₀ ι₃)*(g ι₂ ι₂)*(g ι₃ ι₁)*(g ι₃ ι₂) - (g ι₀ ι₂)*(g ι₂ ι₃)*(g ι₃ ι₁)*(g ι₃ ι₂) + (g ι₀ ι₂)*(g ι₂ ι₁)*(g ι₃ ι₂)*(g ι₃ ι₃) - (g ι₀ ι₁)*(g ι₂ ι₂)*(g ι₃ ι₂)*(g ι₃ ι₃)) * h2

theorem tauTau_33 (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (hg : Sc g) :
    tauMat (tauMat g) ι₃ ι₃ = g ι₃ ι₃ ^ 2 := by
  simp only [tauMat_apply, tauPair_ι₁, tauPair_ι₂, tauPair_ι₃]
  linear_combination ((g ι₃ ι₃)^2) * hg.c02 + ((g ι₃ ι₂)*(g ι₃ ι₃)) * hg.c03 + ((g ι₃ ι₀)*(g ι₃ ι₃)) * hg.c23 + ((g ι₁ ι₃)*(g ι₃ ι₀)*(g ι₃ ι₂)*(g ι₃ ι₃) - (g ι₁ ι₀)*(g ι₃ ι₂)*(g ι₃ ι₃)^2 + (g ι₀ ι₃)*(g ι₂ ι₀)*(g ι₃ ι₂)*(g ι₃ ι₃) - (g ι₀ ι₀)*(g ι₂ ι₃)*(g ι₃ ι₂)*(g ι₃ ι₃)) * h2

theorem tauMat_tauMat (h2 : (2 : R) = 0) {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hg : Sc g) : tauMat (tauMat g) = g.map (fun x => x ^ 2) :=
  matrix_ext16 (tauTau_00 h2 hg) (tauTau_01 h2 hg) (tauTau_02 h2 hg) (tauTau_03 h2 hg) (tauTau_10 h2 hg) (tauTau_11 h2 hg) (tauTau_12 h2 hg) (tauTau_13 h2 hg) (tauTau_20 h2 hg) (tauTau_21 h2 hg) (tauTau_22 h2 hg) (tauTau_23 h2 hg) (tauTau_30 h2 hg) (tauTau_31 h2 hg) (tauTau_32 h2 hg) (tauTau_33 h2 hg)

end TauAlg

end CFSG.QuasithinUnique.Lin2.Five
