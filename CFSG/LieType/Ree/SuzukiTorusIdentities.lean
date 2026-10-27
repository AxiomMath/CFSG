module

public import CFSG.LieType.Ree.SuzukiMatrixIdentities
public import CFSG.Blueprint.CatalogGenerators

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix

variable (a : ℕ) {K : Type} [Field K]

theorem zpow_two_pow_eq (l : Kˣ) : l ^ (2 ^ a : ℤ) = l ^ (2 ^ a : ℕ) := by
  rw [show (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]

theorem suzukiD_eq (l : Kˣ) : suzukiD a l = Matrix.diagonal
    ![(l : K) * (l : K) ^ 2 ^ a, (l : K) ^ 2 ^ a, ((l : K) ^ 2 ^ a)⁻¹,
      ((l : K) * (l : K) ^ 2 ^ a)⁻¹] := by
  rw [suzukiD]
  congr 1
  ext i
  have h1 : l ^ (1 + (2 ^ a : ℤ)) = l * l ^ (2 ^ a : ℕ) := by
    rw [_root_.zpow_add, zpow_one, zpow_two_pow_eq]
  have h2 : l ^ (-(2 ^ a : ℤ)) = (l ^ (2 ^ a : ℕ))⁻¹ := by rw [_root_.zpow_neg, zpow_two_pow_eq]
  have h3 : l ^ (-1 - (2 ^ a : ℤ)) = (l * l ^ (2 ^ a : ℕ))⁻¹ := by
    rw [show -1 - (2 ^ a : ℤ) = -(1 + 2 ^ a) by ring, _root_.zpow_neg, h1]
  fin_cases i <;> simp [h1, h2, h3, zpow_two_pow_eq]

theorem suzukiD_mul (l μ : Kˣ) : suzukiD a l * suzukiD a μ = suzukiD a (l * μ) := by
  rw [suzukiD, suzukiD, suzukiD, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_zpow, mul_comm]

theorem suzukiD_one : suzukiD a (1 : Kˣ) = 1 := by
  rw [suzukiD, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem suzuki_torus_identities
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ l μ : Kˣ, suzukiD a l * suzukiD a μ = suzukiD a (l * μ)) ∧
    suzukiD a (1 : Kˣ) = 1 ∧
    (∀ l μ : Kˣ, suzukiD a l = suzukiD a μ → l = μ) ∧
    (∀ (l : Kˣ) (u v : K), (suzukiD a l)⁻¹ * suzukiS a u v * suzukiD a l =
      suzukiS a ((l : K) * u) ((l : K) ^ (2 ^ (a + 1) + 1) * v)) ∧
    suzukiW K * suzukiW K = 1 ∧
    (∀ l : Kˣ, suzukiW K * suzukiD a l * suzukiW K = suzukiD a l⁻¹) := by
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data a hK
  have hinv : ∀ l : Kˣ, (suzukiD a l)⁻¹ = suzukiD a l⁻¹ := fun l =>
    Matrix.inv_eq_right_inv (by rw [suzukiD_mul, mul_inv_cancel, suzukiD_one])
  refine ⟨suzukiD_mul a, suzukiD_one a, fun l μ h => ?_, fun l u v => ?_,
    suzukiW_mul_self K, fun l => ?_⟩
  · have h0 := congrFun (congrFun h 0) 0
    have h1 := congrFun (congrFun h 1) 1
    rw [suzukiD_eq, suzukiD_eq] at h0 h1
    simp at h0 h1
    apply Units.ext
    have hm : ((l : K) ^ 2 ^ a) ≠ 0 := pow_ne_zero _ l.ne_zero
    rw [h1] at h0
    exact mul_right_cancel₀ (h1 ▸ hm) h0
  · rw [hinv, suzukiD_eq, suzukiD_eq]
    have hx : (l : K) ≠ 0 := l.ne_zero
    have hm : (l : K) ^ 2 ^ a ≠ 0 := pow_ne_zero _ hx
    have hθ : (l : K) ^ 2 ^ (a + 1) = ((l : K) ^ 2 ^ a) ^ 2 := by rw [pow_succ, pow_mul]
    have hθ1 : (l : K) ^ (2 ^ (a + 1) + 1) = ((l : K) ^ 2 ^ a) ^ 2 * (l : K) := by
      rw [pow_succ, hθ]
    have hθθx : (l : K) ^ (2 ^ (a + 1) * 2 ^ (a + 1)) = (l : K) ^ 2 := by rw [pow_mul, hθθ]
    have hN : suzukiN a ((l : K) * u) ((l : K) ^ (2 ^ (a + 1) + 1) * v) =
        ((l : K) * (l : K) ^ 2 ^ a) * suzukiN a u v * ((l : K) * (l : K) ^ 2 ^ a) := by
      have e1 : ((l : K) ^ (2 ^ (a + 1) + 1)) ^ 2 ^ (a + 1) =
          (l : K) ^ 2 * ((l : K) ^ 2 ^ a) ^ 2 := by
        rw [← pow_mul, add_mul, one_mul, pow_add (l : K) (2 ^ (a + 1) * 2 ^ (a + 1)), hθθx, hθ]
      rw [suzukiN, suzukiN, mul_pow, mul_pow, e1, pow_add (l : K) (2 ^ (a + 1)) 2, hθ1, hθ]
      ring
    rw [suzukiS, suzukiS, hN]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-mul_eq_mul_right_iff, -mul_eq_mul_left_iff, diagonal_mul, mul_diagonal,
        Units.val_inv_eq_inv_val, mul_pow, hθ, hθ1, inv_pow]
    all_goals field_simp
  · rw [suzukiD_eq, suzukiD_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four, diagonal, Units.val_inv_eq_inv_val]
    all_goals ring
