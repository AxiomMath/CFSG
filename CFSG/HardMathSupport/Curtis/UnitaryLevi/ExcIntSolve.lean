module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix

@[expose] def rem3 (m : ℤ) : Fin 3 := ⟨(m % 3).toNat, by omega⟩

theorem rem3_cast (m : ℤ) : ((rem3 m : ℕ) : ℤ) = m % 3 := by
  simp only [rem3]; omega

variable {r n : ℕ}

theorem solve_int_fpf (X : Matrix (Fin r) (Fin r) ℤ) (Y : Fin n → Matrix (Fin r) (Fin r) ℤ)
    (hXY : ∀ i, X * Y i = Y i * X) (Θ : Matrix (Fin r) (Fin r) ℤ) (e₂ e₃ l₂ l₃ θ₂ θ₃ : Fin r → ℤ)
    (D1 : (1 - X) * Θ + vecMulVec e₂ l₂ + vecMulVec e₃ l₃ = 1)
    (D2 : (1 - X).mulVec θ₂ = (3 : ℤ) • e₂) (D3 : (1 - X).mulVec θ₃ = (3 : ℤ) • e₃)
    (tab : ∀ a b : Fin 3, ∃ i : Fin n, ∃ d : Fin r → ℤ,
      (1 - X).mulVec d = (1 - Y i).mulVec (((a : ℕ) : ℤ) • e₂ + ((b : ℕ) : ℤ) • e₃)) :
    ∀ c : Fin r → ℤ, ∃ i : Fin n, ∃ d : Fin r → ℤ, (1 - X).mulVec d = (1 - Y i).mulVec c := by
  intro c
  set m₂ := l₂ ⬝ᵥ c with hm₂
  set m₃ := l₃ ⬝ᵥ c with hm₃
  obtain ⟨i, d₀, hd₀⟩ := tab (rem3 m₂) (rem3 m₃)
  set z : Fin r → ℤ := Θ.mulVec c + (m₂ / 3) • θ₂ + (m₃ / 3) • θ₃ with hz
  have hc : c = (1 - X).mulVec z + ((rem3 m₂ : ℕ) : ℤ) • e₂ + ((rem3 m₃ : ℕ) : ℤ) • e₃ := by
    have h1 : c = ((1 - X) * Θ + vecMulVec e₂ l₂ + vecMulVec e₃ l₃).mulVec c := by
      rw [D1, Matrix.one_mulVec]
    have h2 : ((1 - X) * Θ + vecMulVec e₂ l₂ + vecMulVec e₃ l₃).mulVec c =
        (1 - X).mulVec (Θ.mulVec c) + m₂ • e₂ + m₃ • e₃ := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
    have h3 : (1 - X).mulVec z = (1 - X).mulVec (Θ.mulVec c) + (m₂ / 3) • ((3 : ℤ) • e₂) +
        (m₃ / 3) • ((3 : ℤ) • e₃) := by
      rw [hz, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, D2,
        D3]
    rw [h3, rem3_cast, rem3_cast]
    have h4 : m₂ • e₂ = (m₂ / 3) • ((3 : ℤ) • e₂) + (m₂ % 3) • e₂ := by
      rw [smul_smul, ← add_smul]; congr 1; omega
    have h5 : m₃ • e₃ = (m₃ / 3) • ((3 : ℤ) • e₃) + (m₃ % 3) • e₃ := by
      rw [smul_smul, ← add_smul]; congr 1; omega
    conv_lhs => rw [h1, h2, h4, h5]
    abel
  refine ⟨i, (1 - Y i).mulVec z + d₀, ?_⟩
  have hcomm : (1 - X) * (1 - Y i) = (1 - Y i) * (1 - X) := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hXY i]
    abel
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hd₀]
  conv_rhs => rw [hc]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  abel

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
