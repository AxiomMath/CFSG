module

public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LieType.SeitzGeneration.HeisTensor

open Matrix

variable {K : Type*} [Field K]

@[expose] def Zm (ζ : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ζ, 0; 0, 0, ζ ^ 2]

@[expose] def Gj (ζ α : K) (j : ℕ) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, α * ζ ^ (2 * j); 1, 0, 0; 0, ζ ^ j, 0]

@[expose] def adjm (σ : K ≃+* K) (A : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun a b => σ (A b a)

@[expose] def sco (ζ α : K) (S : Matrix (Fin 3) (Fin 3) K) (j : ℕ) : K :=
  3⁻¹ * (S 1 0 + ζ ^ (2 * j) * S 2 1 + ζ ^ j * α⁻¹ * S 0 2)

@[expose] def Qm (σ : K ≃+* K) (ζ α : K) (S : Matrix (Fin 3) (Fin 3) K) (j : ℕ) :
    Matrix (Fin 3) (Fin 3) K :=
  sco ζ α S j • Gj ζ α j + σ (sco ζ α S j) • adjm σ (Gj ζ α j)

section entries

variable {ζ α : K} {j : ℕ}

@[simp] theorem Gj_00 : Gj ζ α j 0 0 = 0 := rfl
@[simp] theorem Gj_01 : Gj ζ α j 0 1 = 0 := rfl
@[simp] theorem Gj_02 : Gj ζ α j 0 2 = α * ζ ^ (2 * j) := rfl
@[simp] theorem Gj_10 : Gj ζ α j 1 0 = 1 := rfl
@[simp] theorem Gj_11 : Gj ζ α j 1 1 = 0 := rfl
@[simp] theorem Gj_12 : Gj ζ α j 1 2 = 0 := rfl
@[simp] theorem Gj_20 : Gj ζ α j 2 0 = 0 := rfl
@[simp] theorem Gj_21 : Gj ζ α j 2 1 = ζ ^ j := rfl
@[simp] theorem Gj_22 : Gj ζ α j 2 2 = 0 := rfl

theorem Zm_apply (ζ : K) (a b : Fin 3) : Zm ζ a b = if a = b then ζ ^ (b : ℕ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [Zm]

theorem adjm_apply (σ : K ≃+* K) (A : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3) :
    adjm σ A a b = σ (A b a) := rfl

end entries

theorem decomp (σ : K ≃+* K) {ζ α : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (hζσ : σ ζ = ζ ^ 2)
    (hα : α ≠ 0) (hασ : σ α = α⁻¹) (h3 : (3 : K) ≠ 0) (S : Matrix (Fin 3) (Fin 3) K)
    (hS : ∀ a b, σ (S b a) = S a b) :
    S = Matrix.diagonal (fun a => S a a) + Qm σ ζ α S 0 + Qm σ ζ α S 1 + Qm σ ζ α S 2 := by
  have h10 : σ (S 1 0) = S 0 1 := hS 0 1
  have h21 : σ (S 2 1) = S 1 2 := hS 1 2
  have h02 : σ (S 0 2) = S 2 0 := hS 2 0
  have h33 : (3 : K) * 3⁻¹ = 1 := mul_inv_cancel₀ h3
  have hαα : α * α⁻¹ = 1 := mul_inv_cancel₀ hα
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hσ3 : σ (3 : K) = 3 := map_ofNat σ 3
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Qm, Matrix.add_apply, Matrix.smul_apply, adjm_apply, Matrix.diagonal_apply,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Gj_00, Gj_01, Gj_02, Gj_10, Gj_11, Gj_12, Gj_20,
      Gj_21, Gj_22, smul_eq_mul, map_zero, map_one, sco, map_mul, map_add, map_inv₀, map_pow,
      hσ3, hζσ, hασ, h10, h21, h02, inv_inv] <;> try simp
  · linear_combination (-S 0 1) * h33 +
      (-(3⁻¹ * S 1 2 * (ζ ^ 6 - ζ ^ 5 + ζ ^ 3 - ζ + 1)) - 3⁻¹ * α * S 2 0 * (ζ ^ 2 - ζ + 1)) * hζ
  · linear_combination (-S 0 2) * h33 + (-(3⁻¹ * S 0 2 * (ζ ^ 3 + 2))) * hζ3 +
      (-(3⁻¹ * S 0 2 * (1 + ζ ^ 3 + ζ ^ 6))) * hαα +
      (-(3⁻¹ * α * S 1 0 * (ζ ^ 2 - ζ + 1)) -
        3⁻¹ * α * S 2 1 * (ζ ^ 6 - ζ ^ 5 + ζ ^ 3 - ζ + 1)) * hζ
  · linear_combination (-S 1 0) * h33 +
      (-(3⁻¹ * S 2 1 * (ζ ^ 2 - ζ + 1)) - 3⁻¹ * α⁻¹ * S 0 2) * hζ
  · linear_combination (-S 1 2) * h33 + (-(3⁻¹ * S 1 2 * (ζ ^ 9 + ζ ^ 6 + 2 * ζ ^ 3 + 2))) * hζ3 +
      (-(3⁻¹ * S 0 1 * (ζ ^ 2 - ζ + 1)) -
        3⁻¹ * α * S 2 0 * (ζ ^ 6 - ζ ^ 5 + ζ ^ 3 - ζ + 1)) * hζ
  · linear_combination (-S 2 0) * h33 + (-(3⁻¹ * S 2 0 * (ζ ^ 9 + ζ ^ 6 + 2 * ζ ^ 3 + 2))) * hζ3 +
      (-(3⁻¹ * S 2 0 * (1 + ζ ^ 6 + ζ ^ 12))) * hαα +
      (-(3⁻¹ * α⁻¹ * S 0 1 * (ζ ^ 6 - ζ ^ 5 + ζ ^ 3 - ζ + 1)) -
        3⁻¹ * α⁻¹ * S 1 2 * (ζ ^ 14 - ζ ^ 13 + ζ ^ 11 - ζ ^ 10 + ζ ^ 8 - ζ ^ 7 + ζ ^ 6 - ζ ^ 4 +
          ζ ^ 3 - ζ + 1)) * hζ
  · linear_combination (-S 2 1) * h33 + (-(3⁻¹ * S 2 1 * (ζ ^ 3 + 2))) * hζ3 +
      (-(3⁻¹ * S 1 0) - 3⁻¹ * α⁻¹ * S 0 2 * (ζ ^ 2 - ζ + 1)) * hζ

theorem Gj_mul_Zm (ζ α : K) (j : ℕ) : Gj ζ α j * Zm ζ = Gj ζ α (j + 1) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Zm_apply] <;> ring

theorem adjm_mul_Gj (σ : K ≃+* K) {ζ α : K} (hζN : σ ζ * ζ = 1) (hαN : σ α * α = 1) (j : ℕ) :
    adjm σ (Gj ζ α j) * Gj ζ α j = 1 := by
  have h1 : σ ζ ^ j * ζ ^ j = 1 := by rw [← mul_pow, hζN, one_pow]
  have h2 : σ α * σ ζ ^ (2 * j) * (α * ζ ^ (2 * j)) = 1 := by
    rw [mul_mul_mul_comm, hαN, ← mul_pow, hζN, one_pow, one_mul]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, adjm_apply, h1, h2]

theorem Gj_mul_adjm (σ : K ≃+* K) {ζ α : K} (hζN : σ ζ * ζ = 1) (hαN : σ α * α = 1) (j : ℕ) :
    Gj ζ α j * adjm σ (Gj ζ α j) = 1 :=
  mul_eq_one_comm.mp (adjm_mul_Gj σ hζN hαN j)

theorem Qm_comm (σ : K ≃+* K) {ζ α : K} (hζN : σ ζ * ζ = 1) (hαN : σ α * α = 1)
    (S : Matrix (Fin 3) (Fin 3) K) (j : ℕ) :
    Qm σ ζ α S j * Gj ζ α j = Gj ζ α j * Qm σ ζ α S j := by
  have h1 := adjm_mul_Gj σ hζN hαN j
  have h2 := Gj_mul_adjm σ hζN hαN j
  simp only [Qm, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h1, h2]

theorem Qm_herm (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (ζ α : K) (S : Matrix (Fin 3) (Fin 3) K)
    (j : ℕ) (a b : Fin 3) : σ (Qm σ ζ α S j b a) = Qm σ ζ α S j a b := by
  simp only [Qm, Matrix.add_apply, Matrix.smul_apply, adjm_apply, smul_eq_mul, map_add, map_mul,
    hσ]
  ring

theorem diag_comm (ζ : K) (d : Fin 3 → K) :
    Matrix.diagonal d * Zm ζ = Zm ζ * Matrix.diagonal d := by
  have : Zm ζ = Matrix.diagonal ![1, ζ, ζ ^ 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Zm, Matrix.diagonal_apply]
  rw [this, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

end CFSG.LieType.SeitzGeneration.HeisTensor
