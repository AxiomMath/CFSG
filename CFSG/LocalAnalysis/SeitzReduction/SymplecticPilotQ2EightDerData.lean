module

public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix

abbrev Sp8dMat : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def sp8dS : Sp8dMat := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def sp8dC1 : Sp8dMat := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def sp8dB1 : Sp8dMat := !![0, 0, 0, 1; 0, 1, 1, 0; 1, 1, 0, 1; 0, 1, 0, 0]

@[expose] def sp8dG : Sp8dMat := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 1, 0, 0]

@[expose] def sp8dH : Sp8dMat := !![0, 1, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 1, 0]

@[expose] def sp8dP1 : Sp8dMat := !![0, 0, 0, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0]

@[expose] def sp8dP1i : Sp8dMat := !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 0, 0, 0]

@[expose] def sp8dR1 : Sp8dMat := !![0, 1, 1, 0; 0, 1, 1, 1; 0, 1, 0, 0; 1, 0, 0, 1]

@[expose] def sp8dR1i : Sp8dMat := !![1, 1, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 1, 1, 0, 0]

@[expose] def sp8dPg : Sp8dMat := !![0, 0, 1, 0; 1, 0, 1, 1; 0, 1, 1, 0; 1, 0, 0, 0]

@[expose] def sp8dPgi : Sp8dMat := !![0, 0, 0, 1; 1, 0, 1, 0; 1, 0, 0, 0; 1, 1, 0, 1]

@[expose] def sp8dRg : Sp8dMat := !![0, 0, 1, 1; 0, 1, 1, 0; 1, 0, 1, 1; 0, 1, 0, 0]

@[expose] def sp8dRgi : Sp8dMat := !![1, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 1; 1, 1, 0, 1]

@[expose] def sp8dPh : Sp8dMat := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

@[expose] def sp8dRh : Sp8dMat := !![0, 0, 1, 0; 1, 0, 0, 1; 0, 1, 1, 0; 1, 0, 0, 0]

@[expose] def sp8dRhi : Sp8dMat := !![0, 0, 0, 1; 1, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 1]

@[expose] def sp8dZ0 : Sp8dMat := !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0]

@[expose] def sp8dY0 : Sp8dMat := !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1]

theorem sp8d_mem_sp :
    sp8dP1 * sp8dS * sp8dP1ᵀ = sp8dS ∧ sp8dR1 * sp8dS * sp8dR1ᵀ = sp8dS ∧
      sp8dPg * sp8dS * sp8dPgᵀ = sp8dS ∧ sp8dRg * sp8dS * sp8dRgᵀ = sp8dS ∧
      sp8dPh * sp8dS * sp8dPhᵀ = sp8dS ∧ sp8dRh * sp8dS * sp8dRhᵀ = sp8dS := by
  decide +kernel

theorem sp8d_inv :
    sp8dP1 * sp8dP1i = 1 ∧ sp8dP1i * sp8dP1 = 1 ∧ sp8dR1 * sp8dR1i = 1 ∧ sp8dR1i * sp8dR1 = 1 ∧
      sp8dPg * sp8dPgi = 1 ∧ sp8dPgi * sp8dPg = 1 ∧ sp8dRg * sp8dRgi = 1 ∧
      sp8dRgi * sp8dRg = 1 ∧ sp8dPh * sp8dPh = 1 ∧ sp8dRh * sp8dRhi = 1 ∧
      sp8dRhi * sp8dRh = 1 := by
  decide +kernel

theorem sp8d_comm :
    sp8dB1 = sp8dP1 * sp8dR1 * sp8dP1i * sp8dR1i ∧ sp8dG = sp8dPg * sp8dRg * sp8dPgi * sp8dRgi ∧
      sp8dH = sp8dPh * sp8dRh * sp8dPh * sp8dRhi := by
  decide +kernel

theorem sp8d_gens_mem_sp :
    sp8dB1 * sp8dS * sp8dB1ᵀ = sp8dS ∧ sp8dG * sp8dS * sp8dGᵀ = sp8dS ∧
      sp8dH * sp8dS * sp8dHᵀ = sp8dS := by
  decide +kernel

theorem sp8d_dihedral :
    sp8dG * sp8dG * sp8dG * sp8dG = 1 ∧ sp8dH * sp8dH = 1 ∧
      sp8dG * sp8dH = sp8dH * (sp8dG * sp8dG * sp8dG) := by
  decide +kernel

@[expose] def Sp8dIsQ5 (Y : Sp8dMat) : Prop :=
  Yᵀ = Y ∧ Y 0 0 = 0 ∧ Y 1 1 = 0 ∧ Y 2 2 = 0 ∧ Y 3 3 = 0 ∧ Y 0 1 = Y 2 3

instance (Y : Sp8dMat) : Decidable (Sp8dIsQ5 Y) := by
  unfold Sp8dIsQ5
  infer_instance

@[expose] def sp8dQ5mk (a b c d e : ZMod 2) : Sp8dMat :=
  !![0, a, b, c; a, 0, d, e; b, d, 0, a; c, e, a, 0]

theorem sp8dIsQ5_mk : ∀ a b c d e : ZMod 2, Sp8dIsQ5 (sp8dQ5mk a b c d e) := by
  decide +kernel

theorem eq_sp8dQ5mk_of_isQ5 {Y : Sp8dMat} (hY : Sp8dIsQ5 Y) :
    Y = sp8dQ5mk (Y 0 1) (Y 0 2) (Y 0 3) (Y 1 2) (Y 1 3) := by
  obtain ⟨hs, h0, h1, h2, h3, h5⟩ := hY
  have e : ∀ a b, Y b a = Y a b := fun a b => by rw [← transpose_apply Y a b, hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp8dQ5mk, h0, h1, h2, h3, h5, e 0 1, e 0 2, e 0 3, e 1 2, e 1 3, e 2 3]

theorem sp8dIsQ5_zero : Sp8dIsQ5 0 := by decide +kernel

theorem sp8dIsQ5_S : Sp8dIsQ5 sp8dS := by decide +kernel

theorem Sp8dIsQ5.add {X Y : Sp8dMat} (hX : Sp8dIsQ5 X) (hY : Sp8dIsQ5 Y) : Sp8dIsQ5 (X + Y) := by
  obtain ⟨hs, h0, h1, h2, h3, h5⟩ := hX
  obtain ⟨hs', h0', h1', h2', h3', h5'⟩ := hY
  refine ⟨by rw [transpose_add, hs, hs'], ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.add_apply, h0, h1, h2, h3, h5, h0', h1', h2', h3', h5']

theorem sp8dIsQ5_conj {T Y : Sp8dMat} (hT : Tᵀ * sp8dS * T = sp8dS) (hY : Sp8dIsQ5 Y) :
    Sp8dIsQ5 (T * Y * Tᵀ) := by
  obtain ⟨hs, h0, h1, h2, h3, h5⟩ := hY
  have e : ∀ a b, Y b a = Y a b := fun a b => by rw [← transpose_apply Y a b, hs]
  have hdiag : ∀ i : Fin 4, (T * Y * Tᵀ) i i = 0 := by
    intro i
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h0, h1, h2, h3,
      e 0 1, e 0 2, e 0 3, e 1 2, e 1 3, e 2 3]
    ring_nf
    reduce_mod_char
  refine ⟨by rw [transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc],
    hdiag 0, hdiag 1, hdiag 2, hdiag 3, ?_⟩
  have h01 := congrFun (congrFun hT 0) 1
  have h02 := congrFun (congrFun hT 0) 2
  have h03 := congrFun (congrFun hT 0) 3
  have h12 := congrFun (congrFun hT 1) 2
  have h13 := congrFun (congrFun hT 1) 3
  have h23 := congrFun (congrFun hT 2) 3
  simp [sp8dS, Matrix.mul_apply, Fin.sum_univ_four] at h01 h02 h03 h12 h13 h23
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h0, h1, h2, h3,
    e 0 1, e 0 2, e 0 3, e 1 2, e 1 3, e 2 3]
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination Y 0 1 * h01 + Y 0 2 * h02 + Y 0 3 * h03 + Y 1 2 * h12 + Y 1 3 * h13 +
    Y 2 3 * h23 + h5 +
    (Y 2 3 - (Y 0 1 * (T 2 0 * T 3 1 + T 2 1 * T 3 0) + Y 0 2 * (T 2 0 * T 3 2 + T 2 2 * T 3 0) +
      Y 0 3 * (T 2 0 * T 3 3 + T 2 3 * T 3 0) + Y 1 2 * (T 2 1 * T 3 2 + T 2 2 * T 3 1) +
      Y 1 3 * (T 2 1 * T 3 3 + T 2 3 * T 3 1) + Y 2 3 * (T 2 2 * T 3 3 + T 2 3 * T 3 2))) * two

@[expose] def sp8dO15L : List Sp8dMat :=
  [!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 1, 0; 0, 0, 1, 1; 1, 1, 0, 0; 0, 1, 0, 0],
    !![0, 0, 1, 1; 0, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
    !![0, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0],
    !![0, 1, 0, 0; 1, 0, 0, 1; 0, 0, 0, 1; 0, 1, 1, 0],
    !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0],
    !![0, 1, 0, 0; 1, 0, 1, 1; 0, 1, 0, 1; 0, 1, 1, 0],
    !![0, 1, 0, 1; 1, 0, 0, 0; 0, 0, 0, 1; 1, 0, 1, 0],
    !![0, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 0],
    !![0, 1, 1, 0; 1, 0, 0, 0; 1, 0, 0, 1; 0, 0, 1, 0],
    !![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 0],
    !![0, 1, 1, 1; 1, 0, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0],
    !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]]

@[expose] def sp8dO15 : Finset Sp8dMat := sp8dO15L.toFinset

@[expose] def sp8dZ15L : List Sp8dMat :=
  [!![0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 1, 1; 0, 1, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, 1; 0, 0, 0, 1; 0, 0, 0, 0; 1, 1, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 1, 0; 1, 1, 0, 0; 0, 0, 0, 0],
    !![0, 0, 1, 1; 0, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0],
    !![0, 0, 1, 1; 0, 0, 1, 1; 1, 1, 0, 0; 1, 1, 0, 0],
    !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0],
    !![0, 1, 0, 1; 1, 0, 1, 1; 0, 1, 0, 1; 1, 1, 1, 0],
    !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 0],
    !![0, 1, 1, 0; 1, 0, 1, 1; 1, 1, 0, 1; 0, 1, 1, 0],
    !![0, 1, 1, 1; 1, 0, 0, 1; 1, 0, 0, 1; 1, 1, 1, 0],
    !![0, 1, 1, 1; 1, 0, 1, 0; 1, 1, 0, 1; 1, 0, 1, 0]]

@[expose] def sp8dZ15 : Finset Sp8dMat := sp8dZ15L.toFinset

@[expose] def sp8dTabA : List (Sp8dMat × Sp8dMat × Sp8dMat) :=
  [(!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]),
    (!![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0],
      !![0, 1, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 1, 1, 0, 0]),
    (!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]),
    (!![0, 0, 1, 0; 0, 0, 1, 1; 1, 1, 0, 0; 0, 1, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 1, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]),
    (!![0, 0, 1, 1; 0, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
      !![0, 1, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 0, 0]),
    (!![0, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0],
      !![0, 1, 0, 1; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 1, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]),
    (!![0, 1, 0, 0; 1, 0, 0, 1; 0, 0, 0, 1; 0, 1, 1, 0],
      !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 0, 0]),
    (!![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0],
      !![0, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0]),
    (!![0, 1, 0, 0; 1, 0, 1, 1; 0, 1, 0, 1; 0, 1, 1, 0],
      !![0, 0, 0, 1; 1, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 1; 1, 0, 0, 0]),
    (!![0, 1, 0, 1; 1, 0, 0, 0; 0, 0, 0, 1; 1, 0, 1, 0],
      !![0, 1, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 1, 0]),
    (!![0, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 0],
      !![0, 1, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 1, 0]),
    (!![0, 1, 1, 0; 1, 0, 0, 0; 1, 0, 0, 1; 0, 0, 1, 0],
      !![1, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1]),
    (!![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 0],
      !![1, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 1]),
    (!![0, 1, 1, 1; 1, 0, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0],
      !![1, 1, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 1, 1]),
    (!![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0],
      !![1, 1, 0, 1; 1, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 1; 1, 0, 1, 1])]

@[expose] def sp8dTabB : List (Sp8dMat × Sp8dMat × Sp8dMat) :=
  [(!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]),
    (!![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0],
      !![0, 1, 0, 1; 1, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 1; 1, 0, 1, 0]),
    (!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
      !![1, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 0, 1]),
    (!![0, 0, 1, 0; 0, 0, 1, 1; 1, 1, 0, 0; 0, 1, 0, 0],
      !![1, 0, 0, 1; 1, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 1; 1, 0, 0, 1]),
    (!![0, 0, 1, 1; 0, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
      !![1, 1, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 1, 1]),
    (!![0, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0],
      !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1]),
    (!![0, 1, 0, 0; 1, 0, 0, 1; 0, 0, 0, 1; 0, 1, 1, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]),
    (!![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0],
      !![0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0]),
    (!![0, 1, 0, 0; 1, 0, 1, 1; 0, 1, 0, 1; 0, 1, 1, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1; 1, 0, 0, 0]),
    (!![0, 1, 0, 1; 1, 0, 0, 0; 0, 0, 0, 1; 1, 0, 1, 0],
      !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]),
    (!![0, 1, 0, 1; 1, 0, 0, 1; 0, 0, 0, 1; 1, 1, 1, 0],
      !![0, 1, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 0, 0]),
    (!![0, 1, 1, 0; 1, 0, 0, 0; 1, 0, 0, 1; 0, 0, 1, 0],
      !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
      !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0]),
    (!![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 0],
      !![0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0],
      !![0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1; 1, 1, 0, 0]),
    (!![0, 1, 1, 1; 1, 0, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0],
      !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 1; 0, 1, 0, 0]),
    (!![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0],
      !![0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 1, 0; 1, 0, 0, 0],
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1; 1, 1, 0, 0])]

theorem sp8dQ5mk_cases : ∀ a b c d e : ZMod 2,
    sp8dQ5mk a b c d e = 0 ∨ sp8dQ5mk a b c d e = sp8dS ∨ sp8dQ5mk a b c d e ∈ sp8dO15L ∨
      sp8dQ5mk a b c d e ∈ sp8dZ15L := by
  decide +kernel

theorem sp8dIsQ5_cases {Y : Sp8dMat} (hY : Sp8dIsQ5 Y) :
    Y = 0 ∨ Y = sp8dS ∨ Y ∈ sp8dO15 ∨ Y ∈ sp8dZ15 := by
  rw [sp8dO15, sp8dZ15, List.mem_toFinset, List.mem_toFinset, eq_sp8dQ5mk_of_isQ5 hY]
  exact sp8dQ5mk_cases _ _ _ _ _

theorem sp8dO15_all : (sp8dO15L.all fun X => decide (Sp8dIsQ5 X) && !(sp8dZ15L.contains X) &&
    !(X == 0) && !(X == sp8dS)) = true := by
  decide +kernel

theorem sp8dO15_isQ5 {X : Sp8dMat} (hX : X ∈ sp8dO15) : Sp8dIsQ5 X := by
  rw [sp8dO15, List.mem_toFinset] at hX
  have h := List.all_eq_true.1 sp8dO15_all X hX
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem sp8dO15_ne_zero {X : Sp8dMat} (hX : X ∈ sp8dO15) : X ≠ 0 := by
  rw [sp8dO15, List.mem_toFinset] at hX
  have h := List.all_eq_true.1 sp8dO15_all X hX
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h.1.2

theorem sp8dO15_ne_S {X : Sp8dMat} (hX : X ∈ sp8dO15) : X ≠ sp8dS := by
  rw [sp8dO15, List.mem_toFinset] at hX
  have h := List.all_eq_true.1 sp8dO15_all X hX
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h.2

@[expose] def sp8dX0 : Sp8dMat := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem sp8dX0_mem : sp8dX0 ∈ sp8dO15 := by decide +kernel

theorem card_sp8dO15_filter :
    (sp8dO15.filter (fun Y => sp8dX0 + Y ∈ sp8dO15)).card = 8 := by
  decide +kernel

theorem sp8dZ15_count : (sp8dZ15L.all fun Z =>
    decide ((sp8dZ15L.filter fun Y => sp8dZ15L.contains (Z + Y)).length ≤ 6)) = true := by
  decide +kernel

theorem card_sp8dZ15_filter_le {Z : Sp8dMat} (hZ : Z ∈ sp8dZ15) :
    (sp8dZ15.filter (fun Y => Z + Y ∈ sp8dZ15)).card ≤ 6 := by
  rw [sp8dZ15, List.mem_toFinset] at hZ
  have h := of_decide_eq_true (List.all_eq_true.1 sp8dZ15_count Z hZ)
  refine le_trans ?_ h
  rw [sp8dZ15, List.filter_toFinset]
  refine (List.toFinset_card_le _).trans (le_of_eq ?_)
  congr 1

theorem sp8dTabA_all : (sp8dTabA.all fun t => decide (t.2.1 * t.2.2 = 1 ∧ t.2.2 * t.2.1 = 1 ∧
    t.2.1 * sp8dS * t.2.1ᵀ = t.1 ∧
    sp8dB1 * (t.2.2 * sp8dS * t.2.2ᵀ) * sp8dB1ᵀ ≠ t.2.2 * sp8dS * t.2.2ᵀ)) = true := by
  decide +kernel

theorem sp8dTabA_cover : (sp8dO15L.all fun X => sp8dTabA.any fun t => t.1 == X) = true := by
  decide +kernel

theorem sp8dTabA_spec {X : Sp8dMat} (hX : X ∈ sp8dO15) : ∃ A A' : Sp8dMat, A * A' = 1 ∧
    A' * A = 1 ∧ A * sp8dS * Aᵀ = X ∧
    sp8dB1 * (A' * sp8dS * A'ᵀ) * sp8dB1ᵀ ≠ A' * sp8dS * A'ᵀ := by
  rw [sp8dO15, List.mem_toFinset] at hX
  obtain ⟨t, ht, htX⟩ := List.any_eq_true.1 (List.all_eq_true.1 sp8dTabA_cover X hX)
  have h := of_decide_eq_true (List.all_eq_true.1 sp8dTabA_all t ht)
  rw [beq_iff_eq] at htX
  rw [htX] at h
  exact ⟨t.2.1, t.2.2, h⟩

theorem sp8dTabB_all : (sp8dTabB.all fun t => decide (t.2.1 * t.2.2 = 1 ∧ t.2.2 * t.2.1 = 1 ∧
    t.2.1 * sp8dC1 * t.2.1ᵀ = sp8dS + t.1)) = true := by
  decide +kernel

theorem sp8dTabB_cover : (sp8dO15L.all fun X => sp8dTabB.any fun t => t.1 == X) = true := by
  decide +kernel

theorem sp8dTabB_spec {X : Sp8dMat} (hX : X ∈ sp8dO15) : ∃ B B' : Sp8dMat, B * B' = 1 ∧
    B' * B = 1 ∧ B * sp8dC1 * Bᵀ = sp8dS + X := by
  rw [sp8dO15, List.mem_toFinset] at hX
  obtain ⟨t, ht, htX⟩ := List.any_eq_true.1 (List.all_eq_true.1 sp8dTabB_cover X hX)
  have h := of_decide_eq_true (List.all_eq_true.1 sp8dTabB_all t ht)
  rw [beq_iff_eq] at htX
  rw [htX] at h
  exact ⟨t.2.1, t.2.2, h⟩

@[expose] def Sp8dInS (Y : Sp8dMat) : Prop := Y = 0 ∨ Y = sp8dS

instance (Y : Sp8dMat) : Decidable (Sp8dInS Y) := by
  unfold Sp8dInS
  infer_instance

@[expose] def sp8dSym (a b c d e f g h i j : ZMod 2) : Sp8dMat :=
  !![a, b, c, d; b, e, f, g; c, f, h, i; d, g, i, j]

theorem eq_sp8dSym {Y : Sp8dMat} (hY : Yᵀ = Y) :
    Y = sp8dSym (Y 0 0) (Y 0 1) (Y 0 2) (Y 0 3) (Y 1 1) (Y 1 2) (Y 1 3) (Y 2 2) (Y 2 3)
      (Y 3 3) := by
  have e : ∀ a b, Y b a = Y a b := fun a b => by rw [← transpose_apply Y a b, hY]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp8dSym, e 0 1, e 0 2, e 0 3, e 1 2, e 1 3, e 2 3]

theorem sp8d_fixModS_sym : ∀ a b c d e f g h i j : ZMod 2,
    Sp8dInS (sp8dG * sp8dSym a b c d e f g h i j * sp8dGᵀ + sp8dSym a b c d e f g h i j) →
    Sp8dInS (sp8dH * sp8dSym a b c d e f g h i j * sp8dHᵀ + sp8dSym a b c d e f g h i j) →
    Sp8dInS (sp8dSym a b c d e f g h i j) ∨
      Sp8dInS (sp8dSym a b c d e f g h i j + sp8dZ0) ∨
      Sp8dInS (sp8dSym a b c d e f g h i j + sp8dY0) ∨
      Sp8dInS (sp8dSym a b c d e f g h i j + sp8dY0 + sp8dZ0) := by
  decide +kernel

theorem sp8d_fixModS {Y : Sp8dMat} (hY : Yᵀ = Y) (hg : Sp8dInS (sp8dG * Y * sp8dGᵀ + Y))
    (hh : Sp8dInS (sp8dH * Y * sp8dHᵀ + Y)) :
    Sp8dInS Y ∨ Sp8dInS (Y + sp8dZ0) ∨ Sp8dInS (Y + sp8dY0) ∨
      Sp8dInS (Y + sp8dY0 + sp8dZ0) := by
  rw [eq_sp8dSym hY] at hg hh ⊢
  exact sp8d_fixModS_sym _ _ _ _ _ _ _ _ _ _ hg hh

theorem sp8d_prog_y0 : sp8dB1 * sp8dY0 * sp8dB1ᵀ +
    sp8dG * (sp8dG * (sp8dB1 * sp8dY0 * sp8dB1ᵀ) * sp8dGᵀ) * sp8dGᵀ = sp8dZ0 := by
  decide +kernel

theorem sp8d_prog_u : (sp8dY0 + sp8dZ0) + sp8dB1 * (sp8dY0 + sp8dZ0) * sp8dB1ᵀ +
    sp8dG * (sp8dB1 * (sp8dY0 + sp8dZ0) * sp8dB1ᵀ) * sp8dGᵀ = sp8dZ0 := by
  decide +kernel

theorem sp8dQ5mk_eq_basis : ∀ a b c d e : ZMod 2,
    sp8dQ5mk a b c d e = a • sp8dS + b • (sp8dB1 * sp8dZ0 * sp8dB1ᵀ) + c • sp8dZ0 +
      d • (sp8dB1 * (sp8dB1 * sp8dZ0 * sp8dB1ᵀ) * sp8dB1ᵀ) +
      e • (sp8dG * (sp8dB1 * sp8dZ0 * sp8dB1ᵀ) * sp8dGᵀ) := by
  decide +kernel

theorem sp8dZ0_isQ5 : Sp8dIsQ5 sp8dZ0 := by decide +kernel

theorem sp8dZ0_ne : sp8dZ0 ≠ 0 ∧ sp8dZ0 ≠ sp8dS := by decide +kernel

theorem sp8dB1_irred : ∀ v0 v1 v2 v3 : ZMod 2, ![v0, v1, v2, v3] ≠ 0 → ∀ k : Fin 4,
    ∃ c0 c1 c2 c3 : ZMod 2, Pi.single k 1 = c0 • ![v0, v1, v2, v3] +
      c1 • (sp8dB1 *ᵥ ![v0, v1, v2, v3]) + c2 • (sp8dB1 *ᵥ (sp8dB1 *ᵥ ![v0, v1, v2, v3])) +
      c3 • (sp8dB1 *ᵥ (sp8dB1 *ᵥ (sp8dB1 *ᵥ ![v0, v1, v2, v3]))) := by
  decide +kernel

end CFSG.SeitzReduction.SymplecticPilot
