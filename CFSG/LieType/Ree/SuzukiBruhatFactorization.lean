module

public import CFSG.LieType.Ree.SuzukiMatrixIdentities
public import CFSG.LieType.Ree.SuzukiNorm

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint Matrix

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiS_eq_explicit (x y X Y : K) (hX : x ^ 2 ^ (a + 1) = X)
    (hY : y ^ 2 ^ (a + 1) = Y) :
    suzukiS a x y = !![1, 0, 0, 0; x, 1, 0, 0; y, X, 1, 0;
      X * x ^ 2 + x * y + Y, X * x + y, x, 1] := by
  rw [suzukiS, suzukiN, pow_add x (2 ^ (a + 1)) 2, pow_succ x (2 ^ (a + 1)), hX, hY]

theorem suzukiW_eq : suzukiW K = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW]

theorem units_zpow_add_mul_card [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : Kˣ)
    (n k : ℤ) : x ^ (n + k * (2 ^ (2 * a + 1) - 1)) = x ^ n := by
  have h1 : x ^ ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have hcast : ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) = 2 ^ (2 * a + 1) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [_root_.zpow_add, mul_comm k, _root_.zpow_mul, ← hcast, h1, _root_.one_zpow, mul_one]

theorem suzukiD_two_sub_theta [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ) :
    suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) =
      !![(t : K), 0, 0, 0; 0, (t : K) ^ 2 ^ (a + 1) * (t : K)⁻¹, 0, 0;
        0, 0, (t : K) * ((t : K) ^ 2 ^ (a + 1))⁻¹, 0; 0, 0, 0, (t : K)⁻¹] := by
  have e1 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (1 + (2 ^ a : ℤ)) = t := by
    rw [← _root_.zpow_mul, show (2 - 2 ^ (a + 1) : ℤ) * (1 + 2 ^ a) =
      1 + (-1) * (2 ^ (2 * a + 1) - 1) by ring, units_zpow_add_mul_card hK, zpow_one]
  have e2 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (2 ^ a : ℤ) = t ^ 2 ^ (a + 1) * t⁻¹ := by
    rw [← _root_.zpow_mul, show (2 - 2 ^ (a + 1) : ℤ) * 2 ^ a =
      ((2 ^ (a + 1) : ℕ) : ℤ) - 1 + (-1) * (2 ^ (2 * a + 1) - 1) by push_cast; ring,
      units_zpow_add_mul_card hK, _root_.zpow_sub_one, zpow_natCast]
  have e3 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (-(2 ^ a : ℤ)) = t * (t ^ 2 ^ (a + 1))⁻¹ := by
    rw [_root_.zpow_neg, e2, _root_.mul_inv_rev, inv_inv, mul_comm]
  have e4 : (t ^ (2 - 2 ^ (a + 1) : ℤ)) ^ (-1 - (2 ^ a : ℤ)) = t⁻¹ := by
    rw [show (-1 - (2 ^ a : ℤ)) = -(1 + 2 ^ a) by ring, _root_.zpow_neg, e1]
  rw [suzukiD, e1, e2, e3, e4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_inv_eq_inv_val]

theorem suzukiBruhat_entry_00 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    (1) = V * τ * s ^ 2 + v ^ 2 * τ * s * S + v ^ 2 * V * τ * s ^ 2 * S + u * v * U * τ * s * S +
      (2) * u * v * U * V * τ * s ^ 2 * S + u ^ 2 * U ^ 2 * V * τ * s ^ 2 * S + u ^ 2 * v ^ 2 * U *
      τ * s ^ 2 * S + (2) * u ^ 3 * v * U ^ 2 * τ * s ^ 2 * S + u ^ 4 * U ^ 3 * τ * s ^ 2 * S := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + v ^ 2 * τ * T * s * S ^ 2 + u * v * U *
      τ * T * s * S ^ 2) * hts + ((-1) + V * τ * s ^ 2 + v ^ 2 * τ * s * S + (-1) * v ^ 2 * τ ^ 2 *
      s ^ 2 * S + u * v * U * τ * s * S + (-1) * u * v * U * τ ^ 2 * s ^ 2 * S) * hTS + (τ * T * s ^
      2 * S + (-1) * v ^ 2 * τ * s ^ 2 * S + (-2) * v ^ 2 * V * s ^ 2 * S + u * v * T * s ^ 2 * S +
      (-1) * u * v * U * τ * s ^ 2 * S + (-3) * u * v * U * V * s ^ 2 * S + (-1) * u * v ^ 3 * s ^ 2
      * S + u ^ 2 * U * T * s ^ 2 * S + (-1) * u ^ 2 * U ^ 2 * V * s ^ 2 * S + (-3) * u ^ 2 * v ^ 2
      * U * s ^ 2 * S + (-3) * u ^ 3 * v * U ^ 2 * s ^ 2 * S + (-1) * u ^ 4 * U ^ 3 * s ^ 2 * S) *
      ht + (u * v * V * s ^ 2 * S + u ^ 2 * U * V * s ^ 2 * S + u ^ 2 * v ^ 2 * s ^ 2 * S + (2) * u
      ^ 3 * v * U * s ^ 2 * S + u ^ 4 * U ^ 2 * s ^ 2 * S) * hT + ((-1) * v ^ 2 * V ^ 2 * s ^ 2 * S
      + (-1) * u * v * U * V ^ 2 * s ^ 2 * S + (-1) * u * v ^ 3 * V * s ^ 2 * S + (-3) * u ^ 2 * v ^
      2 * U * V * s ^ 2 * S + (-2) * u ^ 3 * v * U ^ 2 * V * s ^ 2 * S + (-1) * u ^ 3 * v ^ 3 * U *
      s ^ 2 * S + (-2) * u ^ 4 * v ^ 2 * U ^ 2 * s ^ 2 * S + (-1) * u ^ 5 * v * U ^ 3 * s ^ 2 * S) *
      h2

theorem suzukiBruhat_entry_01 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    u = v * τ * S + v * V * τ * s * S + u * U * V * τ * s * S + u ^ 2 * v * U * τ * s * S + u ^ 3 *
      U ^ 2 * τ * s * S := by
  linear_combination (v * τ * T * S ^ 2 + (-1) * u * T * S) * hts + (v * τ * S + (-1) * v * τ ^ 2 *
      s * S + (-1) * u) * hTS + ((-1) * v * τ * s * S + (-2) * v * V * s * S + u * T * s * S + (-1)
      * u * U * V * s * S + (-1) * u * v ^ 2 * s * S + (-2) * u ^ 2 * v * U * s * S + (-1) * u ^ 3 *
      U ^ 2 * s * S) * ht + (u * V * s * S + u ^ 2 * v * s * S + u ^ 3 * U * s * S) * hT + ((-1) * v
      * V ^ 2 * s * S + (-1) * u * v ^ 2 * V * s * S + (-2) * u ^ 2 * v * U * V * s * S + (-1) * u ^
      3 * v ^ 2 * U * s * S + (-1) * u ^ 4 * v * U ^ 2 * s * S) * h2

theorem suzukiBruhat_entry_02 {R : Type*} [CommRing R] (u v U τ s : R)
    (hts : τ * s = 1) :
    v + u * U = v * τ * s + u * U * τ * s := by
  linear_combination ((-1) * v + (-1) * u * U) * hts

theorem suzukiBruhat_entry_03 {R : Type*} [CommRing R] (u v U V τ : R)
    (ht : τ = U * u ^ 2 + u * v + V) :
    V + u * v + u ^ 2 * U = τ := by
  linear_combination ((-1)) * ht

theorem suzukiBruhat_entry_10 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * T * s * S + v * V * τ * s ^ 3 + v ^ 3 * τ * s ^ 2 * S + v ^ 3 * V * τ * s ^ 3 * S + u *
      v ^ 2 * U * τ * s ^ 2 * S + (2) * u * v ^ 2 * U * V * τ * s ^ 3 * S + u ^ 2 * v * U ^ 2 * V *
      τ * s ^ 3 * S + u ^ 2 * v ^ 3 * U * τ * s ^ 3 * S + (2) * u ^ 3 * v ^ 2 * U ^ 2 * τ * s ^ 3 *
      S + u ^ 4 * v * U ^ 3 * τ * s ^ 3 * S := by
  linear_combination (v * T ^ 2 * s * S ^ 2 + v * τ * T ^ 2 * s ^ 2 * S ^ 2 + v ^ 3 * τ * T * s ^ 2
      * S ^ 2 + u * v ^ 2 * U * τ * T * s ^ 2 * S ^ 2) * hts + (v * T * s * S + (-1) * v * τ ^ 2 * T
      * s ^ 3 * S + v * V * τ * s ^ 3 + v ^ 3 * τ * s ^ 2 * S + (-1) * v ^ 3 * τ ^ 2 * s ^ 3 * S + u
      * v ^ 2 * U * τ * s ^ 2 * S + (-1) * u * v ^ 2 * U * τ ^ 2 * s ^ 3 * S) * hTS + ((-1) * v * τ
      * T * s ^ 3 * S + (-2) * v * V * T * s ^ 3 * S + (-1) * v ^ 3 * τ * s ^ 3 * S + (-2) * v ^ 3 *
      V * s ^ 3 * S + (-1) * u * v ^ 2 * T * s ^ 3 * S + (-1) * u * v ^ 2 * U * τ * s ^ 3 * S + (-3)
      * u * v ^ 2 * U * V * s ^ 3 * S + (-1) * u * v ^ 4 * s ^ 3 * S + (-1) * u ^ 2 * v * U * T * s
      ^ 3 * S + (-1) * u ^ 2 * v * U ^ 2 * V * s ^ 3 * S + (-3) * u ^ 2 * v ^ 3 * U * s ^ 3 * S +
      (-3) * u ^ 3 * v ^ 2 * U ^ 2 * s ^ 3 * S + (-1) * u ^ 4 * v * U ^ 3 * s ^ 3 * S) * ht + ((-2)
      * v * V ^ 2 * s ^ 3 * S + (-3) * u * v ^ 2 * V * s ^ 3 * S + (-3) * u ^ 2 * v * U * V * s ^ 3
      * S + (-1) * u ^ 2 * v ^ 3 * s ^ 3 * S + (-2) * u ^ 3 * v ^ 2 * U * s ^ 3 * S + (-1) * u ^ 4 *
      v * U ^ 2 * s ^ 3 * S) * hT + ((-1) * v * U * V ^ 3 * s ^ 3 * S + (-2) * v ^ 3 * V ^ 2 * s ^ 3
      * S + (-3) * u * v ^ 2 * U * V ^ 2 * s ^ 3 * S + (-3) * u * v ^ 4 * V * s ^ 3 * S + (-3) * u ^
      2 * v * U ^ 2 * V ^ 2 * s ^ 3 * S + (-6) * u ^ 2 * v ^ 3 * U * V * s ^ 3 * S + (-1) * u ^ 2 *
      v ^ 5 * s ^ 3 * S + (-6) * u ^ 3 * v ^ 2 * U ^ 2 * V * s ^ 3 * S + (-3) * u ^ 3 * v ^ 4 * U *
      s ^ 3 * S + (-3) * u ^ 4 * v * U ^ 3 * V * s ^ 3 * S + (-4) * u ^ 4 * v ^ 3 * U ^ 2 * s ^ 3 *
      S + (-3) * u ^ 5 * v ^ 2 * U ^ 3 * s ^ 3 * S + (-1) * u ^ 6 * v * U ^ 4 * s ^ 3 * S) * h2

theorem suzukiBruhat_entry_11 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    (1) = V * T * s * S + v ^ 2 * τ * s * S + v ^ 2 * V * τ * s ^ 2 * S + u * v * U * V * τ * s ^ 2
      * S + u ^ 2 * U * T * s * S + u ^ 2 * v ^ 2 * U * τ * s ^ 2 * S + u ^ 3 * v * U ^ 2 * τ * s ^
      2 * S := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + V * T ^ 2 * s * S ^ 2 + v ^ 2 * τ * T *
      s * S ^ 2 + u ^ 2 * U * T ^ 2 * s * S ^ 2) * hts + ((-1) + V * T * s * S + (-1) * V * τ * T *
      s ^ 2 * S + v ^ 2 * τ * s * S + (-1) * v ^ 2 * τ ^ 2 * s ^ 2 * S + u ^ 2 * U * T * s * S +
      (-1) * u ^ 2 * U * τ * T * s ^ 2 * S) * hTS + (τ * T * s ^ 2 * S + (-1) * v ^ 2 * τ * s ^ 2 *
      S + (-2) * v ^ 2 * V * s ^ 2 * S + u * v * T * s ^ 2 * S + (-1) * u * v * U * V * s ^ 2 * S +
      (-1) * u * v ^ 3 * s ^ 2 * S + (-2) * u ^ 2 * v ^ 2 * U * s ^ 2 * S + (-1) * u ^ 3 * v * U ^ 2
      * s ^ 2 * S) * ht + (u * v * V * s ^ 2 * S + u ^ 2 * v ^ 2 * s ^ 2 * S + u ^ 3 * v * U * s ^ 2
      * S) * hT + ((-1) * v ^ 2 * V ^ 2 * s ^ 2 * S + (-1) * u * v ^ 3 * V * s ^ 2 * S + (-2) * u ^
      2 * v ^ 2 * U * V * s ^ 2 * S + (-1) * u ^ 3 * v ^ 3 * U * s ^ 2 * S + (-1) * u ^ 4 * v ^ 2 *
      U ^ 2 * s ^ 2 * S) * h2

theorem suzukiBruhat_entry_12 {R : Type*} [CommRing R] (u v U V τ T s : R)
    (hts : τ * s = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U * V + v ^ 2) (h2
    : (2 : R) = 0) :
    U = T * s + v ^ 2 * τ * s ^ 2 + u * v * U * τ * s ^ 2 := by
  linear_combination (T * s + (-1) * U + (-1) * U * τ * s) * hts + ((-1) * T * s ^ 2 + U * τ * s ^ 2
      + U * V * s ^ 2 + (-1) * v ^ 2 * s ^ 2 + u ^ 2 * U ^ 2 * s ^ 2) * ht + ((-1) * V * s ^ 2 +
      (-1) * u * v * s ^ 2 + (-1) * u ^ 2 * U * s ^ 2) * hT + ((-1) * v ^ 2 * V * s ^ 2 + (-1) * u *
      v ^ 3 * s ^ 2 + (-1) * u ^ 2 * v ^ 2 * U * s ^ 2) * h2

theorem suzukiBruhat_entry_13 {R : Type*} [CommRing R] (v τ s : R)
    (hts : τ * s = 1) :
    v = v * τ * s := by
  linear_combination ((-1) * v) * hts

theorem suzukiBruhat_entry_20 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * τ * s * S + v * V * T * s * S ^ 2 + u * V * τ * s ^ 3 + u * U * τ * s * S + u * v ^ 2 *
      τ * s ^ 2 * S + u * v ^ 2 * V * τ * s ^ 3 * S + u ^ 2 * v * U * τ * s ^ 2 * S + (2) * u ^ 2 *
      v * U * V * τ * s ^ 3 * S + u ^ 3 * U ^ 2 * V * τ * s ^ 3 * S + u ^ 3 * v ^ 2 * U * τ * s ^ 3
      * S + (2) * u ^ 4 * v * U ^ 2 * τ * s ^ 3 * S + u ^ 5 * U ^ 3 * τ * s ^ 3 * S := by
  linear_combination (v * τ * T ^ 2 * s * S ^ 3 + v * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 3 + v * V * T ^ 3
      * s * S ^ 4 + v * V * τ * T ^ 3 * s ^ 2 * S ^ 4 + u * U * τ * T ^ 2 * s * S ^ 3 + u * U * τ ^
      2 * T ^ 2 * s ^ 2 * S ^ 3 + u * v ^ 2 * τ * T ^ 2 * s ^ 2 * S ^ 3 + u ^ 2 * v * U * τ * T ^ 2
      * s ^ 2 * S ^ 3) * hts + (v * τ * s * S + v * τ * T * s * S ^ 2 + (-1) * v * τ ^ 3 * T * s ^ 3
      * S ^ 2 + v * V * T * s * S ^ 2 + v * V * T ^ 2 * s * S ^ 3 + (-1) * v * V * τ ^ 2 * T * s ^ 3
      * S ^ 2 + (-1) * v * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + u * V * τ * s ^ 3 + u * V * τ * T * s
      ^ 3 * S + u * U * τ * s * S + u * U * τ * T * s * S ^ 2 + (-1) * u * U * τ ^ 3 * T * s ^ 3 * S
      ^ 2 + u * v ^ 2 * τ * s ^ 2 * S + u * v ^ 2 * τ * T * s ^ 2 * S ^ 2 + (-1) * u * v ^ 2 * τ ^ 2
      * T * s ^ 3 * S ^ 2 + u * v ^ 2 * V * τ * s ^ 3 * S + u ^ 2 * v * U * τ * s ^ 2 * S + u ^ 2 *
      v * U * τ * T * s ^ 2 * S ^ 2 + (-1) * u ^ 2 * v * U * τ ^ 2 * T * s ^ 3 * S ^ 2 + (2) * u ^ 2
      * v * U * V * τ * s ^ 3 * S + u ^ 3 * U ^ 2 * V * τ * s ^ 3 * S + u ^ 3 * v ^ 2 * U * τ * s ^
      3 * S + (2) * u ^ 4 * v * U ^ 2 * τ * s ^ 3 * S + u ^ 5 * U ^ 3 * τ * s ^ 3 * S) * hTS + ((-1)
      * v * τ ^ 2 * T * s ^ 3 * S ^ 2 + (-2) * v * V * τ * T * s ^ 3 * S ^ 2 + (-2) * v * V ^ 2 * T
      * s ^ 3 * S ^ 2 + (-1) * u * V * T ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * U * τ ^ 2 * T * s ^ 3 * S
      ^ 2 + (-1) * u * U * V * τ * T * s ^ 3 * S ^ 2 + (-1) * u * U * V ^ 2 * T * s ^ 3 * S ^ 2 +
      (-2) * u * v ^ 2 * τ * T * s ^ 3 * S ^ 2 + (-5) * u * v ^ 2 * V * T * s ^ 3 * S ^ 2 + (-3) * u
      ^ 2 * v * U * τ * T * s ^ 3 * S ^ 2 + (-8) * u ^ 2 * v * U * V * T * s ^ 3 * S ^ 2 + (-2) * u
      ^ 2 * v ^ 3 * T * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U ^ 2 * τ * T * s ^ 3 * S ^ 2 + (-3) * u ^ 3
      * U ^ 2 * V * T * s ^ 3 * S ^ 2 + (-6) * u ^ 3 * v ^ 2 * U * T * s ^ 3 * S ^ 2 + (-6) * u ^ 4
      * v * U ^ 2 * T * s ^ 3 * S ^ 2 + (-2) * u ^ 5 * U ^ 3 * T * s ^ 3 * S ^ 2) * ht + ((-2) * v *
      V ^ 3 * s ^ 3 * S ^ 2 + (-1) * u * V ^ 2 * T * s ^ 3 * S ^ 2 + (-2) * u * U * V ^ 3 * s ^ 3 *
      S ^ 2 + (-8) * u * v ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * V * T * s ^ 3 * S ^ 2 +
      (-12) * u ^ 2 * v * U * V ^ 2 * s ^ 3 * S ^ 2 + (-8) * u ^ 2 * v ^ 3 * V * s ^ 3 * S ^ 2 +
      (-1) * u ^ 3 * U * V * T * s ^ 3 * S ^ 2 + (-6) * u ^ 3 * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 +
      (-20) * u ^ 3 * v ^ 2 * U * V * s ^ 3 * S ^ 2 + (-2) * u ^ 3 * v ^ 4 * s ^ 3 * S ^ 2 + (-18) *
      u ^ 4 * v * U ^ 2 * V * s ^ 3 * S ^ 2 + (-8) * u ^ 4 * v ^ 3 * U * s ^ 3 * S ^ 2 + (-6) * u ^
      5 * U ^ 3 * V * s ^ 3 * S ^ 2 + (-12) * u ^ 5 * v ^ 2 * U ^ 2 * s ^ 3 * S ^ 2 + (-8) * u ^ 6 *
      v * U ^ 3 * s ^ 3 * S ^ 2 + (-2) * u ^ 7 * U ^ 4 * s ^ 3 * S ^ 2) * hT + ((-1) * v * U * V ^ 4
      * s ^ 3 * S ^ 2 + (-1) * v ^ 3 * V ^ 3 * s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V ^ 4 * s ^ 3 * S
      ^ 2 + (-5) * u * v ^ 2 * U * V ^ 3 * s ^ 3 * S ^ 2 + (-4) * u * v ^ 4 * V ^ 2 * s ^ 3 * S ^ 2
      + (-7) * u ^ 2 * v * U ^ 2 * V ^ 3 * s ^ 3 * S ^ 2 + (-10) * u ^ 2 * v ^ 3 * U * V ^ 2 * s ^ 3
      * S ^ 2 + (-4) * u ^ 2 * v ^ 5 * V * s ^ 3 * S ^ 2 + (-4) * u ^ 3 * U ^ 3 * V ^ 3 * s ^ 3 * S
      ^ 2 + (-17) * u ^ 3 * v ^ 2 * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-11) * u ^ 3 * v ^ 4 * U * V *
      s ^ 3 * S ^ 2 + (-1) * u ^ 3 * v ^ 6 * s ^ 3 * S ^ 2 + (-15) * u ^ 4 * v * U ^ 3 * V ^ 2 * s ^
      3 * S ^ 2 + (-17) * u ^ 4 * v ^ 3 * U ^ 2 * V * s ^ 3 * S ^ 2 + (-4) * u ^ 4 * v ^ 5 * U * s ^
      3 * S ^ 2 + (-6) * u ^ 5 * U ^ 4 * V ^ 2 * s ^ 3 * S ^ 2 + (-19) * u ^ 5 * v ^ 2 * U ^ 3 * V *
      s ^ 3 * S ^ 2 + (-7) * u ^ 5 * v ^ 4 * U ^ 2 * s ^ 3 * S ^ 2 + (-13) * u ^ 6 * v * U ^ 4 * V *
      s ^ 3 * S ^ 2 + (-8) * u ^ 6 * v ^ 3 * U ^ 3 * s ^ 3 * S ^ 2 + (-4) * u ^ 7 * U ^ 5 * V * s ^
      3 * S ^ 2 + (-7) * u ^ 7 * v ^ 2 * U ^ 4 * s ^ 3 * S ^ 2 + (-4) * u ^ 8 * v * U ^ 5 * s ^ 3 *
      S ^ 2 + (-1) * u ^ 9 * U ^ 6 * s ^ 3 * S ^ 2) * h2

theorem suzukiBruhat_entry_21 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = τ * S + V ^ 2 * T * s * S ^ 2 + u * v * τ * s * S + u * v * V * τ * s ^ 2 * S + u ^ 2 * U *
      V * T * s * S ^ 2 + u ^ 2 * U * V * τ * s ^ 2 * S + u ^ 3 * v * U * τ * s ^ 2 * S + u ^ 4 * U
      ^ 2 * τ * s ^ 2 * S := by
  linear_combination (τ * T ^ 2 * S ^ 3 + τ ^ 2 * T ^ 2 * s * S ^ 3 + V ^ 2 * T ^ 3 * s * S ^ 4 + u
      * v * τ * T ^ 2 * s * S ^ 3 + u ^ 2 * U * V * T ^ 3 * s * S ^ 4) * hts + (τ * S + τ * T * S ^
      2 + (-1) * τ ^ 3 * T * s ^ 2 * S ^ 2 + V ^ 2 * T * s * S ^ 2 + V ^ 2 * T ^ 2 * s * S ^ 3 +
      (-1) * V ^ 2 * τ * T * s ^ 2 * S ^ 2 + (-1) * V ^ 2 * τ * T ^ 2 * s ^ 2 * S ^ 3 + u * v * τ *
      s * S + u * v * τ * T * s * S ^ 2 + (-1) * u * v * τ ^ 2 * T * s ^ 2 * S ^ 2 + u * v * V * τ *
      s ^ 2 * S + u ^ 2 * U * V * T * s * S ^ 2 + u ^ 2 * U * V * T ^ 2 * s * S ^ 3 + u ^ 2 * U * V
      * τ * s ^ 2 * S + (-1) * u ^ 2 * U * V * τ * T * s ^ 2 * S ^ 2 + (-1) * u ^ 2 * U * V * τ * T
      ^ 2 * s ^ 2 * S ^ 3 + u ^ 3 * v * U * τ * s ^ 2 * S + u ^ 4 * U ^ 2 * τ * s ^ 2 * S) * hTS +
      ((-1) * τ ^ 2 * T * s ^ 2 * S ^ 2 + (-1) * V * τ * T * s ^ 2 * S ^ 2 + (-2) * V ^ 2 * T * s ^
      2 * S ^ 2 + (-2) * u * v * τ * T * s ^ 2 * S ^ 2 + (-4) * u * v * V * T * s ^ 2 * S ^ 2 + (-1)
      * u ^ 2 * U * τ * T * s ^ 2 * S ^ 2 + (-4) * u ^ 2 * U * V * T * s ^ 2 * S ^ 2 + (-2) * u ^ 2
      * v ^ 2 * T * s ^ 2 * S ^ 2 + (-4) * u ^ 3 * v * U * T * s ^ 2 * S ^ 2 + (-2) * u ^ 4 * U ^ 2
      * T * s ^ 2 * S ^ 2) * ht + ((-2) * V ^ 3 * s ^ 2 * S ^ 2 + (-6) * u * v * V ^ 2 * s ^ 2 * S ^
      2 + (-6) * u ^ 2 * U * V ^ 2 * s ^ 2 * S ^ 2 + (-6) * u ^ 2 * v ^ 2 * V * s ^ 2 * S ^ 2 +
      (-12) * u ^ 3 * v * U * V * s ^ 2 * S ^ 2 + (-2) * u ^ 3 * v ^ 3 * s ^ 2 * S ^ 2 + (-6) * u ^
      4 * U ^ 2 * V * s ^ 2 * S ^ 2 + (-6) * u ^ 4 * v ^ 2 * U * s ^ 2 * S ^ 2 + (-6) * u ^ 5 * v *
      U ^ 2 * s ^ 2 * S ^ 2 + (-2) * u ^ 6 * U ^ 3 * s ^ 2 * S ^ 2) * hT + ((-1) * U * V ^ 4 * s ^ 2
      * S ^ 2 + (-1) * v ^ 2 * V ^ 3 * s ^ 2 * S ^ 2 + (-3) * u * v * U * V ^ 3 * s ^ 2 * S ^ 2 +
      (-3) * u * v ^ 3 * V ^ 2 * s ^ 2 * S ^ 2 + (-4) * u ^ 2 * U ^ 2 * V ^ 3 * s ^ 2 * S ^ 2 + (-6)
      * u ^ 2 * v ^ 2 * U * V ^ 2 * s ^ 2 * S ^ 2 + (-3) * u ^ 2 * v ^ 4 * V * s ^ 2 * S ^ 2 + (-9)
      * u ^ 3 * v * U ^ 2 * V ^ 2 * s ^ 2 * S ^ 2 + (-7) * u ^ 3 * v ^ 3 * U * V * s ^ 2 * S ^ 2 +
      (-1) * u ^ 3 * v ^ 5 * s ^ 2 * S ^ 2 + (-6) * u ^ 4 * U ^ 3 * V ^ 2 * s ^ 2 * S ^ 2 + (-9) * u
      ^ 4 * v ^ 2 * U ^ 2 * V * s ^ 2 * S ^ 2 + (-3) * u ^ 4 * v ^ 4 * U * s ^ 2 * S ^ 2 + (-9) * u
      ^ 5 * v * U ^ 3 * V * s ^ 2 * S ^ 2 + (-4) * u ^ 5 * v ^ 3 * U ^ 2 * s ^ 2 * S ^ 2 + (-4) * u
      ^ 6 * U ^ 4 * V * s ^ 2 * S ^ 2 + (-4) * u ^ 6 * v ^ 2 * U ^ 3 * s ^ 2 * S ^ 2 + (-3) * u ^ 7
      * v * U ^ 4 * s ^ 2 * S ^ 2 + (-1) * u ^ 8 * U ^ 5 * s ^ 2 * S ^ 2) * h2

theorem suzukiBruhat_entry_22 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) :
    (1) = V * T * s * S + u * v * τ * s ^ 2 + u ^ 2 * U * τ * s ^ 2 := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + V * T ^ 2 * s * S ^ 2) * hts + ((-1) + V
      * T * s * S + (-1) * V * τ * T * s ^ 2 * S + u * v * τ * s ^ 2 + u ^ 2 * U * τ * s ^ 2) * hTS
      + (τ * T * s ^ 2 * S) * ht

theorem suzukiBruhat_entry_23 {R : Type*} [CommRing R] (u τ s : R)
    (hts : τ * s = 1) :
    u = u * τ * s := by
  linear_combination ((-1) * u) * hts

theorem suzukiBruhat_entry_30 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = s + U * V * τ * s ^ 2 * S + v ^ 2 * τ * s ^ 2 * S + v ^ 2 * V * T * s ^ 2 * S ^ 2 + v ^ 2 *
      V ^ 2 * τ * s ^ 4 * S + v ^ 2 * U * τ * s * S ^ 2 + v ^ 2 * U * V * τ * s ^ 2 * S ^ 2 + v ^ 4
      * V * τ * s ^ 3 * S ^ 2 + v ^ 4 * V ^ 2 * τ * s ^ 4 * S ^ 2 + u * v * T * s ^ 2 * S + u * v *
      V * τ * s ^ 4 + u * v * U * τ * s ^ 2 * S + u * v * U ^ 2 * τ * s * S ^ 2 + (2) * u * v * U ^
      2 * V * τ * s ^ 2 * S ^ 2 + u * v ^ 3 * τ * s ^ 3 * S + u * v ^ 3 * V * τ * s ^ 4 * S + u * v
      ^ 3 * U * V * τ * s ^ 3 * S ^ 2 + (2) * u * v ^ 3 * U * V ^ 2 * τ * s ^ 4 * S ^ 2 + u ^ 2 * U
      ^ 3 * V * τ * s ^ 2 * S ^ 2 + u ^ 2 * v ^ 2 * U * τ * s ^ 3 * S + (2) * u ^ 2 * v ^ 2 * U * V
      * τ * s ^ 4 * S + u ^ 2 * v ^ 2 * U ^ 2 * τ * s ^ 2 * S ^ 2 + u ^ 2 * v ^ 2 * U ^ 2 * V ^ 2 *
      τ * s ^ 4 * S ^ 2 + u ^ 2 * v ^ 4 * U * V * τ * s ^ 4 * S ^ 2 + u ^ 3 * v * U ^ 2 * V * τ * s
      ^ 4 * S + (2) * u ^ 3 * v * U ^ 3 * τ * s ^ 2 * S ^ 2 + u ^ 3 * v ^ 3 * U * τ * s ^ 4 * S +
      (2) * u ^ 3 * v ^ 3 * U ^ 2 * V * τ * s ^ 4 * S ^ 2 + u ^ 4 * U ^ 4 * τ * s ^ 2 * S ^ 2 + (2)
      * u ^ 4 * v ^ 2 * U ^ 2 * τ * s ^ 4 * S + u ^ 4 * v ^ 2 * U ^ 3 * V * τ * s ^ 4 * S ^ 2 + u ^
      5 * v * U ^ 3 * τ * s ^ 4 * S := by
  linear_combination (T ^ 2 * s * S ^ 2 + τ * T ^ 2 * s ^ 2 * S ^ 2 + τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 2
      + U * V * τ * T ^ 2 * s ^ 2 * S ^ 3 + U * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + v ^ 2 * τ * T ^
      2 * s ^ 2 * S ^ 3 + v ^ 2 * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + v ^ 2 * V * T ^ 3 * s ^ 2 * S ^ 4
      + v ^ 2 * V * τ * T ^ 3 * s ^ 3 * S ^ 4 + v ^ 2 * U * τ * T ^ 2 * s * S ^ 4 + v ^ 2 * U * τ ^
      2 * T ^ 2 * s ^ 2 * S ^ 4 + v ^ 2 * U * τ ^ 3 * T ^ 2 * s ^ 3 * S ^ 4 + v ^ 2 * U * V * τ * T
      ^ 2 * s ^ 2 * S ^ 4 + v ^ 2 * U * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 4 + v ^ 4 * V * τ * T ^ 2 *
      s ^ 3 * S ^ 4 + u * v * T ^ 3 * s ^ 2 * S ^ 3 + u * v * τ * T ^ 3 * s ^ 3 * S ^ 3 + u * v * U
      * τ * T ^ 2 * s ^ 2 * S ^ 3 + u * v * U * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 3 + u * v * U ^ 2 * τ *
      T ^ 2 * s * S ^ 4 + u * v * U ^ 2 * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 4 + u * v * U ^ 2 * τ ^ 3 * T
      ^ 2 * s ^ 3 * S ^ 4 + (2) * u * v * U ^ 2 * V * τ * T ^ 2 * s ^ 2 * S ^ 4 + (2) * u * v * U ^
      2 * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 4 + u * v ^ 3 * τ * T ^ 2 * s ^ 3 * S ^ 3 + u * v ^ 3 * U
      * V * τ * T ^ 2 * s ^ 3 * S ^ 4 + u ^ 2 * U ^ 3 * V * τ * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 2 * U ^
      3 * V * τ ^ 2 * T ^ 2 * s ^ 3 * S ^ 4 + u ^ 2 * v ^ 2 * U * τ * T ^ 2 * s ^ 3 * S ^ 3 + u ^ 2
      * v ^ 2 * U ^ 2 * τ * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 2 * v ^ 2 * U ^ 2 * τ ^ 2 * T ^ 2 * s ^ 3 *
      S ^ 4 + (2) * u ^ 3 * v * U ^ 3 * τ * T ^ 2 * s ^ 2 * S ^ 4 + (2) * u ^ 3 * v * U ^ 3 * τ ^ 2
      * T ^ 2 * s ^ 3 * S ^ 4 + u ^ 4 * U ^ 4 * τ * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 4 * U ^ 4 * τ ^ 2 *
      T ^ 2 * s ^ 3 * S ^ 4) * hts + (s + T * s * S + U * V * τ * s ^ 2 * S + U * V * τ * T * s ^ 2
      * S ^ 2 + (-1) * U * V * τ ^ 3 * T * s ^ 4 * S ^ 2 + v ^ 2 * τ * s ^ 2 * S + v ^ 2 * τ * T * s
      ^ 2 * S ^ 2 + (-1) * v ^ 2 * τ ^ 3 * T * s ^ 4 * S ^ 2 + v ^ 2 * V * T * s ^ 2 * S ^ 2 + v ^ 2
      * V * T ^ 2 * s ^ 2 * S ^ 3 + (-1) * v ^ 2 * V * τ ^ 2 * T * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * V
      * τ ^ 2 * T ^ 2 * s ^ 4 * S ^ 3 + v ^ 2 * V ^ 2 * τ * s ^ 4 * S + v ^ 2 * U * τ * s * S ^ 2 +
      v ^ 2 * U * τ * T * s * S ^ 3 + (-1) * v ^ 2 * U * τ ^ 4 * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * U *
      τ ^ 4 * T * s ^ 4 * S ^ 3 + v ^ 2 * U * V * τ * s ^ 2 * S ^ 2 + v ^ 2 * U * V * τ * T * s ^ 2
      * S ^ 3 + (-1) * v ^ 2 * U * V * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * U * V * τ ^ 3 * T * s
      ^ 4 * S ^ 3 + v ^ 4 * V * τ * s ^ 3 * S ^ 2 + v ^ 4 * V * τ * T * s ^ 3 * S ^ 3 + (-1) * v ^ 4
      * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-1) * v ^ 4 * V * τ ^ 2 * T * s ^ 4 * S ^ 3 + u * v * T * s ^ 2
      * S + u * v * T ^ 2 * s ^ 2 * S ^ 2 + (-1) * u * v * τ ^ 2 * T ^ 2 * s ^ 4 * S ^ 2 + u * v * V
      * τ * s ^ 4 + u * v * V * τ * T * s ^ 4 * S + u * v * U * τ * s ^ 2 * S + u * v * U * τ * T *
      s ^ 2 * S ^ 2 + (-1) * u * v * U * τ ^ 3 * T * s ^ 4 * S ^ 2 + u * v * U ^ 2 * τ * s * S ^ 2 +
      u * v * U ^ 2 * τ * T * s * S ^ 3 + (-1) * u * v * U ^ 2 * τ ^ 4 * s ^ 4 * S ^ 2 + (-1) * u *
      v * U ^ 2 * τ ^ 4 * T * s ^ 4 * S ^ 3 + (2) * u * v * U ^ 2 * V * τ * s ^ 2 * S ^ 2 + (2) * u
      * v * U ^ 2 * V * τ * T * s ^ 2 * S ^ 3 + (-2) * u * v * U ^ 2 * V * τ ^ 3 * s ^ 4 * S ^ 2 +
      (-2) * u * v * U ^ 2 * V * τ ^ 3 * T * s ^ 4 * S ^ 3 + u * v ^ 3 * τ * s ^ 3 * S + u * v ^ 3 *
      τ * T * s ^ 3 * S ^ 2 + (-1) * u * v ^ 3 * τ ^ 2 * T * s ^ 4 * S ^ 2 + u * v ^ 3 * V * τ * s ^
      4 * S + u * v ^ 3 * U * V * τ * s ^ 3 * S ^ 2 + u * v ^ 3 * U * V * τ * T * s ^ 3 * S ^ 3 +
      (-1) * u * v ^ 3 * U * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-1) * u * v ^ 3 * U * V * τ ^ 2 * T * s ^
      4 * S ^ 3 + u ^ 2 * U ^ 3 * V * τ * s ^ 2 * S ^ 2 + u ^ 2 * U ^ 3 * V * τ * T * s ^ 2 * S ^ 3
      + (-1) * u ^ 2 * U ^ 3 * V * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V * τ ^ 3 * T * s
      ^ 4 * S ^ 3 + u ^ 2 * v ^ 2 * U * τ * s ^ 3 * S + u ^ 2 * v ^ 2 * U * τ * T * s ^ 3 * S ^ 2 +
      (-1) * u ^ 2 * v ^ 2 * U * τ ^ 2 * T * s ^ 4 * S ^ 2 + (2) * u ^ 2 * v ^ 2 * U * V * τ * s ^ 4
      * S + u ^ 2 * v ^ 2 * U ^ 2 * τ * s ^ 2 * S ^ 2 + u ^ 2 * v ^ 2 * U ^ 2 * τ * T * s ^ 2 * S ^
      3 + (-1) * u ^ 2 * v ^ 2 * U ^ 2 * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * v ^ 2 * U ^ 2 * τ ^
      3 * T * s ^ 4 * S ^ 3 + u ^ 3 * v * U ^ 2 * V * τ * s ^ 4 * S + (2) * u ^ 3 * v * U ^ 3 * τ *
      s ^ 2 * S ^ 2 + (2) * u ^ 3 * v * U ^ 3 * τ * T * s ^ 2 * S ^ 3 + (-2) * u ^ 3 * v * U ^ 3 * τ
      ^ 3 * s ^ 4 * S ^ 2 + (-2) * u ^ 3 * v * U ^ 3 * τ ^ 3 * T * s ^ 4 * S ^ 3 + u ^ 3 * v ^ 3 * U
      * τ * s ^ 4 * S + u ^ 4 * U ^ 4 * τ * s ^ 2 * S ^ 2 + u ^ 4 * U ^ 4 * τ * T * s ^ 2 * S ^ 3 +
      (-1) * u ^ 4 * U ^ 4 * τ ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 4 * τ ^ 3 * T * s ^ 4 * S ^
      3 + (2) * u ^ 4 * v ^ 2 * U ^ 2 * τ * s ^ 4 * S + u ^ 5 * v * U ^ 3 * τ * s ^ 4 * S) * hTS +
      ((-1) * τ ^ 2 * T ^ 2 * s ^ 4 * S ^ 2 + (-1) * V * τ * T ^ 2 * s ^ 4 * S ^ 2 + (-1) * V ^ 2 *
      T ^ 2 * s ^ 4 * S ^ 2 + (-1) * U * V * τ ^ 2 * T * s ^ 4 * S ^ 2 + (-1) * U * V ^ 2 * τ * T *
      s ^ 4 * S ^ 2 + (-1) * U * V ^ 3 * T * s ^ 4 * S ^ 2 + (-1) * v ^ 2 * τ ^ 2 * T * s ^ 4 * S ^
      2 + (-2) * v ^ 2 * V * τ * T * s ^ 4 * S ^ 2 + (-3) * v ^ 2 * V ^ 2 * T * s ^ 4 * S ^ 2 + (-1)
      * v ^ 2 * U * τ ^ 3 * s ^ 4 * S ^ 2 + (-2) * v ^ 2 * U * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-2) * v
      ^ 2 * U * V ^ 2 * τ * s ^ 4 * S ^ 2 + (-2) * v ^ 2 * U * V ^ 3 * s ^ 4 * S ^ 2 + (-1) * v ^ 4
      * V * τ * s ^ 4 * S ^ 2 + (-2) * v ^ 4 * V ^ 2 * s ^ 4 * S ^ 2 + (-2) * u * v * τ * T ^ 2 * s
      ^ 4 * S ^ 2 + (-4) * u * v * V * T ^ 2 * s ^ 4 * S ^ 2 + (-1) * u * v * U * τ ^ 2 * T * s ^ 4
      * S ^ 2 + (-2) * u * v * U * V * τ * T * s ^ 4 * S ^ 2 + (-3) * u * v * U * V ^ 2 * T * s ^ 4
      * S ^ 2 + (-1) * u * v * U ^ 2 * τ ^ 3 * s ^ 4 * S ^ 2 + (-3) * u * v * U ^ 2 * V * τ ^ 2 * s
      ^ 4 * S ^ 2 + (-3) * u * v * U ^ 2 * V ^ 2 * τ * s ^ 4 * S ^ 2 + (-3) * u * v * U ^ 2 * V ^ 3
      * s ^ 4 * S ^ 2 + (-2) * u * v ^ 3 * τ * T * s ^ 4 * S ^ 2 + (-5) * u * v ^ 3 * V * T * s ^ 4
      * S ^ 2 + (-1) * u * v ^ 3 * U * τ ^ 2 * s ^ 4 * S ^ 2 + (-4) * u * v ^ 3 * U * V * τ * s ^ 4
      * S ^ 2 + (-8) * u * v ^ 3 * U * V ^ 2 * s ^ 4 * S ^ 2 + (-1) * u * v ^ 5 * V * s ^ 4 * S ^ 2
      + (-1) * u ^ 2 * U * τ * T ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 2 * U * V * T ^ 2 * s ^ 4 * S ^ 2
      + (-1) * u ^ 2 * U ^ 2 * V * τ * T * s ^ 4 * S ^ 2 + (-2) * u ^ 2 * U ^ 2 * V ^ 2 * T * s ^ 4
      * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V * τ ^ 2 * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V ^ 2 * τ
      * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * U ^ 3 * V ^ 3 * s ^ 4 * S ^ 2 + (-2) * u ^ 2 * v ^ 2 * T ^ 2
      * s ^ 4 * S ^ 2 + (-3) * u ^ 2 * v ^ 2 * U * τ * T * s ^ 4 * S ^ 2 + (-9) * u ^ 2 * v ^ 2 * U
      * V * T * s ^ 4 * S ^ 2 + (-3) * u ^ 2 * v ^ 2 * U ^ 2 * τ ^ 2 * s ^ 4 * S ^ 2 + (-8) * u ^ 2
      * v ^ 2 * U ^ 2 * V * τ * s ^ 4 * S ^ 2 + (-14) * u ^ 2 * v ^ 2 * U ^ 2 * V ^ 2 * s ^ 4 * S ^
      2 + (-2) * u ^ 2 * v ^ 4 * T * s ^ 4 * S ^ 2 + (-1) * u ^ 2 * v ^ 4 * U * τ * s ^ 4 * S ^ 2 +
      (-7) * u ^ 2 * v ^ 4 * U * V * s ^ 4 * S ^ 2 + (-3) * u ^ 3 * v * U * T ^ 2 * s ^ 4 * S ^ 2 +
      (-1) * u ^ 3 * v * U ^ 2 * τ * T * s ^ 4 * S ^ 2 + (-5) * u ^ 3 * v * U ^ 2 * V * T * s ^ 4 *
      S ^ 2 + (-3) * u ^ 3 * v * U ^ 3 * τ ^ 2 * s ^ 4 * S ^ 2 + (-7) * u ^ 3 * v * U ^ 3 * V * τ *
      s ^ 4 * S ^ 2 + (-11) * u ^ 3 * v * U ^ 3 * V ^ 2 * s ^ 4 * S ^ 2 + (-6) * u ^ 3 * v ^ 3 * U *
      T * s ^ 4 * S ^ 2 + (-4) * u ^ 3 * v ^ 3 * U ^ 2 * τ * s ^ 4 * S ^ 2 + (-18) * u ^ 3 * v ^ 3 *
      U ^ 2 * V * s ^ 4 * S ^ 2 + (-1) * u ^ 3 * v ^ 5 * U * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 2 *
      T ^ 2 * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 3 * V * T * s ^ 4 * S ^ 2 + (-1) * u ^ 4 * U ^ 4 *
      τ ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 4 * U ^ 4 * V * τ * s ^ 4 * S ^ 2 + (-3) * u ^ 4 * U ^ 4 *
      V ^ 2 * s ^ 4 * S ^ 2 + (-6) * u ^ 4 * v ^ 2 * U ^ 2 * T * s ^ 4 * S ^ 2 + (-6) * u ^ 4 * v ^
      2 * U ^ 3 * τ * s ^ 4 * S ^ 2 + (-22) * u ^ 4 * v ^ 2 * U ^ 3 * V * s ^ 4 * S ^ 2 + (-5) * u ^
      4 * v ^ 4 * U ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 5 * v * U ^ 3 * T * s ^ 4 * S ^ 2 + (-4) * u ^
      5 * v * U ^ 4 * τ * s ^ 4 * S ^ 2 + (-13) * u ^ 5 * v * U ^ 4 * V * s ^ 4 * S ^ 2 + (-10) * u
      ^ 5 * v ^ 3 * U ^ 3 * s ^ 4 * S ^ 2 + (-1) * u ^ 6 * U ^ 5 * τ * s ^ 4 * S ^ 2 + (-3) * u ^ 6
      * U ^ 5 * V * s ^ 4 * S ^ 2 + (-10) * u ^ 6 * v ^ 2 * U ^ 4 * s ^ 4 * S ^ 2 + (-5) * u ^ 7 * v
      * U ^ 5 * s ^ 4 * S ^ 2 + (-1) * u ^ 8 * U ^ 6 * s ^ 4 * S ^ 2) * ht + ((-1) * V ^ 3 * T * s ^
      4 * S ^ 2 + (-2) * U * V ^ 4 * s ^ 4 * S ^ 2 + (-4) * v ^ 2 * V ^ 3 * s ^ 4 * S ^ 2 + (-5) * u
      * v * V ^ 2 * T * s ^ 4 * S ^ 2 + (-9) * u * v * U * V ^ 3 * s ^ 4 * S ^ 2 + (-13) * u * v ^ 3
      * V ^ 2 * s ^ 4 * S ^ 2 + (-3) * u ^ 2 * U * V ^ 2 * T * s ^ 4 * S ^ 2 + (-7) * u ^ 2 * U ^ 2
      * V ^ 3 * s ^ 4 * S ^ 2 + (-6) * u ^ 2 * v ^ 2 * V * T * s ^ 4 * S ^ 2 + (-24) * u ^ 2 * v ^ 2
      * U * V ^ 2 * s ^ 4 * S ^ 2 + (-13) * u ^ 2 * v ^ 4 * V * s ^ 4 * S ^ 2 + (-9) * u ^ 3 * v * U
      * V * T * s ^ 4 * S ^ 2 + (-24) * u ^ 3 * v * U ^ 2 * V ^ 2 * s ^ 4 * S ^ 2 + (-2) * u ^ 3 * v
      ^ 3 * T * s ^ 4 * S ^ 2 + (-31) * u ^ 3 * v ^ 3 * U * V * s ^ 4 * S ^ 2 + (-4) * u ^ 3 * v ^ 5
      * s ^ 4 * S ^ 2 + (-3) * u ^ 4 * U ^ 2 * V * T * s ^ 4 * S ^ 2 + (-9) * u ^ 4 * U ^ 3 * V ^ 2
      * s ^ 4 * S ^ 2 + (-5) * u ^ 4 * v ^ 2 * U * T * s ^ 4 * S ^ 2 + (-34) * u ^ 4 * v ^ 2 * U ^ 2
      * V * s ^ 4 * S ^ 2 + (-13) * u ^ 4 * v ^ 4 * U * s ^ 4 * S ^ 2 + (-4) * u ^ 5 * v * U ^ 2 * T
      * s ^ 4 * S ^ 2 + (-21) * u ^ 5 * v * U ^ 3 * V * s ^ 4 * S ^ 2 + (-18) * u ^ 5 * v ^ 3 * U ^
      2 * s ^ 4 * S ^ 2 + (-1) * u ^ 6 * U ^ 3 * T * s ^ 4 * S ^ 2 + (-5) * u ^ 6 * U ^ 4 * V * s ^
      4 * S ^ 2 + (-14) * u ^ 6 * v ^ 2 * U ^ 3 * s ^ 4 * S ^ 2 + (-6) * u ^ 7 * v * U ^ 4 * s ^ 4 *
      S ^ 2 + (-1) * u ^ 8 * U ^ 5 * s ^ 4 * S ^ 2) * hT + ((-1) * U ^ 2 * V ^ 5 * s ^ 4 * S ^ 2 +
      (-4) * v ^ 2 * U * V ^ 4 * s ^ 4 * S ^ 2 + (-3) * v ^ 4 * V ^ 3 * s ^ 4 * S ^ 2 + (-6) * u * v
      * U ^ 2 * V ^ 4 * s ^ 4 * S ^ 2 + (-16) * u * v ^ 3 * U * V ^ 3 * s ^ 4 * S ^ 2 + (-8) * u * v
      ^ 5 * V ^ 2 * s ^ 4 * S ^ 2 + (-5) * u ^ 2 * U ^ 3 * V ^ 4 * s ^ 4 * S ^ 2 + (-27) * u ^ 2 * v
      ^ 2 * U ^ 2 * V ^ 3 * s ^ 4 * S ^ 2 + (-27) * u ^ 2 * v ^ 4 * U * V ^ 2 * s ^ 4 * S ^ 2 + (-7)
      * u ^ 2 * v ^ 6 * V * s ^ 4 * S ^ 2 + (-24) * u ^ 3 * v * U ^ 3 * V ^ 3 * s ^ 4 * S ^ 2 +
      (-54) * u ^ 3 * v ^ 3 * U ^ 2 * V ^ 2 * s ^ 4 * S ^ 2 + (-22) * u ^ 3 * v ^ 5 * U * V * s ^ 4
      * S ^ 2 + (-2) * u ^ 3 * v ^ 7 * s ^ 4 * S ^ 2 + (-10) * u ^ 4 * U ^ 4 * V ^ 3 * s ^ 4 * S ^ 2
      + (-57) * u ^ 4 * v ^ 2 * U ^ 3 * V ^ 2 * s ^ 4 * S ^ 2 + (-45) * u ^ 4 * v ^ 4 * U ^ 2 * V *
      s ^ 4 * S ^ 2 + (-7) * u ^ 4 * v ^ 6 * U * s ^ 4 * S ^ 2 + (-36) * u ^ 5 * v * U ^ 4 * V ^ 2 *
      s ^ 4 * S ^ 2 + (-60) * u ^ 5 * v ^ 3 * U ^ 3 * V * s ^ 4 * S ^ 2 + (-14) * u ^ 5 * v ^ 5 * U
      ^ 2 * s ^ 4 * S ^ 2 + (-10) * u ^ 6 * U ^ 5 * V ^ 2 * s ^ 4 * S ^ 2 + (-49) * u ^ 6 * v ^ 2 *
      U ^ 4 * V * s ^ 4 * S ^ 2 + (-21) * u ^ 6 * v ^ 4 * U ^ 3 * s ^ 4 * S ^ 2 + (-24) * u ^ 7 * v
      * U ^ 5 * V * s ^ 4 * S ^ 2 + (-22) * u ^ 7 * v ^ 3 * U ^ 4 * s ^ 4 * S ^ 2 + (-5) * u ^ 8 * U
      ^ 6 * V * s ^ 4 * S ^ 2 + (-15) * u ^ 8 * v ^ 2 * U ^ 5 * s ^ 4 * S ^ 2 + (-6) * u ^ 9 * v * U
      ^ 6 * s ^ 4 * S ^ 2 + (-1) * u ^ 10 * U ^ 7 * s ^ 4 * S ^ 2) * h2

theorem suzukiBruhat_entry_31 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * τ * s * S + v * V ^ 2 * T * s ^ 2 * S ^ 2 + v * U * τ * S ^ 2 + v * U * V * τ * s * S ^
      2 + v ^ 3 * V * τ * s ^ 2 * S ^ 2 + v ^ 3 * V ^ 2 * τ * s ^ 3 * S ^ 2 + u * V * T * s ^ 2 * S
      + u * U ^ 2 * V * τ * s * S ^ 2 + u * v ^ 2 * τ * s ^ 2 * S + u * v ^ 2 * V * τ * s ^ 3 * S +
      u * v ^ 2 * U * V ^ 2 * τ * s ^ 3 * S ^ 2 + u ^ 2 * v * U * V * T * s ^ 2 * S ^ 2 + u ^ 2 * v
      * U * V * τ * s ^ 3 * S + u ^ 2 * v * U ^ 2 * τ * s * S ^ 2 + u ^ 2 * v ^ 3 * U * V * τ * s ^
      3 * S ^ 2 + u ^ 3 * U * T * s ^ 2 * S + u ^ 3 * U ^ 3 * τ * s * S ^ 2 + u ^ 3 * v ^ 2 * U * τ
      * s ^ 3 * S + u ^ 3 * v ^ 2 * U ^ 2 * V * τ * s ^ 3 * S ^ 2 + u ^ 4 * v * U ^ 2 * τ * s ^ 3 *
      S := by
  linear_combination (v * τ * T ^ 2 * s * S ^ 3 + v * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 3 + v * V ^ 2 * T
      ^ 3 * s ^ 2 * S ^ 4 + v * U * τ * T ^ 2 * S ^ 4 + v * U * τ ^ 2 * T ^ 2 * s * S ^ 4 + v * U *
      τ ^ 3 * T ^ 2 * s ^ 2 * S ^ 4 + v * U * V * τ * T ^ 2 * s * S ^ 4 + v * U * V * τ ^ 2 * T ^ 2
      * s ^ 2 * S ^ 4 + v ^ 3 * V * τ * T ^ 2 * s ^ 2 * S ^ 4 + u * V * T ^ 3 * s ^ 2 * S ^ 3 + u *
      U ^ 2 * V * τ * T ^ 2 * s * S ^ 4 + u * U ^ 2 * V * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 4 + u * v ^ 2
      * τ * T ^ 2 * s ^ 2 * S ^ 3 + u ^ 2 * v * U * V * T ^ 3 * s ^ 2 * S ^ 4 + u ^ 2 * v * U ^ 2 *
      τ * T ^ 2 * s * S ^ 4 + u ^ 2 * v * U ^ 2 * τ ^ 2 * T ^ 2 * s ^ 2 * S ^ 4 + u ^ 3 * U * T ^ 3
      * s ^ 2 * S ^ 3 + u ^ 3 * U ^ 3 * τ * T ^ 2 * s * S ^ 4 + u ^ 3 * U ^ 3 * τ ^ 2 * T ^ 2 * s ^
      2 * S ^ 4) * hts + (v * τ * s * S + v * τ * T * s * S ^ 2 + (-1) * v * τ ^ 3 * T * s ^ 3 * S ^
      2 + v * V ^ 2 * T * s ^ 2 * S ^ 2 + v * V ^ 2 * T ^ 2 * s ^ 2 * S ^ 3 + (-1) * v * V ^ 2 * τ *
      T * s ^ 3 * S ^ 2 + (-1) * v * V ^ 2 * τ * T ^ 2 * s ^ 3 * S ^ 3 + v * U * τ * S ^ 2 + v * U *
      τ * T * S ^ 3 + (-1) * v * U * τ ^ 4 * s ^ 3 * S ^ 2 + (-1) * v * U * τ ^ 4 * T * s ^ 3 * S ^
      3 + v * U * V * τ * s * S ^ 2 + v * U * V * τ * T * s * S ^ 3 + (-1) * v * U * V * τ ^ 3 * s ^
      3 * S ^ 2 + (-1) * v * U * V * τ ^ 3 * T * s ^ 3 * S ^ 3 + v ^ 3 * V * τ * s ^ 2 * S ^ 2 + v ^
      3 * V * τ * T * s ^ 2 * S ^ 3 + (-1) * v ^ 3 * V * τ ^ 2 * s ^ 3 * S ^ 2 + (-1) * v ^ 3 * V *
      τ ^ 2 * T * s ^ 3 * S ^ 3 + u * V * T * s ^ 2 * S + u * V * T ^ 2 * s ^ 2 * S ^ 2 + (-1) * u *
      V * τ * T ^ 2 * s ^ 3 * S ^ 2 + u * U ^ 2 * V * τ * s * S ^ 2 + u * U ^ 2 * V * τ * T * s * S
      ^ 3 + (-1) * u * U ^ 2 * V * τ ^ 3 * s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V * τ ^ 3 * T * s ^ 3
      * S ^ 3 + u * v ^ 2 * τ * s ^ 2 * S + u * v ^ 2 * τ * T * s ^ 2 * S ^ 2 + (-1) * u * v ^ 2 * τ
      ^ 2 * T * s ^ 3 * S ^ 2 + u * v ^ 2 * V * τ * s ^ 3 * S + u ^ 2 * v * U * V * T * s ^ 2 * S ^
      2 + u ^ 2 * v * U * V * T ^ 2 * s ^ 2 * S ^ 3 + u ^ 2 * v * U * V * τ * s ^ 3 * S + (-1) * u ^
      2 * v * U * V * τ * T * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * U * V * τ * T ^ 2 * s ^ 3 * S ^ 3 +
      u ^ 2 * v * U ^ 2 * τ * s * S ^ 2 + u ^ 2 * v * U ^ 2 * τ * T * s * S ^ 3 + (-1) * u ^ 2 * v *
      U ^ 2 * τ ^ 3 * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * U ^ 2 * τ ^ 3 * T * s ^ 3 * S ^ 3 + u ^ 3 *
      U * T * s ^ 2 * S + u ^ 3 * U * T ^ 2 * s ^ 2 * S ^ 2 + (-1) * u ^ 3 * U * τ * T ^ 2 * s ^ 3 *
      S ^ 2 + u ^ 3 * U ^ 3 * τ * s * S ^ 2 + u ^ 3 * U ^ 3 * τ * T * s * S ^ 3 + (-1) * u ^ 3 * U ^
      3 * τ ^ 3 * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U ^ 3 * τ ^ 3 * T * s ^ 3 * S ^ 3 + u ^ 3 * v ^ 2 *
      U * τ * s ^ 3 * S + u ^ 4 * v * U ^ 2 * τ * s ^ 3 * S) * hTS + ((-1) * v * τ ^ 2 * T * s ^ 3 *
      S ^ 2 + (-1) * v * V * τ * T * s ^ 3 * S ^ 2 + (-2) * v * V ^ 2 * T * s ^ 3 * S ^ 2 + (-1) * v
      * U * τ ^ 3 * s ^ 3 * S ^ 2 + (-2) * v * U * V * τ ^ 2 * s ^ 3 * S ^ 2 + (-2) * v * U * V ^ 2
      * τ * s ^ 3 * S ^ 2 + (-2) * v * U * V ^ 3 * s ^ 3 * S ^ 2 + (-1) * v ^ 3 * V * τ * s ^ 3 * S
      ^ 2 + (-2) * v ^ 3 * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * V * T ^ 2 * s ^ 3 * S ^ 2 + (-1) * u *
      U ^ 2 * V * τ ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V ^ 2 * τ * s ^ 3 * S ^ 2 + (-1) * u *
      U ^ 2 * V ^ 3 * s ^ 3 * S ^ 2 + (-2) * u * v ^ 2 * τ * T * s ^ 3 * S ^ 2 + (-4) * u * v ^ 2 *
      V * T * s ^ 3 * S ^ 2 + (-1) * u * v ^ 2 * U * τ ^ 2 * s ^ 3 * S ^ 2 + (-3) * u * v ^ 2 * U *
      V * τ * s ^ 3 * S ^ 2 + (-6) * u * v ^ 2 * U * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u * v ^ 4 * V *
      s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * U * τ * T * s ^ 3 * S ^ 2 + (-4) * u ^ 2 * v * U * V * T *
      s ^ 3 * S ^ 2 + (-2) * u ^ 2 * v * U ^ 2 * τ ^ 2 * s ^ 3 * S ^ 2 + (-5) * u ^ 2 * v * U ^ 2 *
      V * τ * s ^ 3 * S ^ 2 + (-8) * u ^ 2 * v * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-2) * u ^ 2 * v ^
      3 * T * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v ^ 3 * U * τ * s ^ 3 * S ^ 2 + (-6) * u ^ 2 * v ^ 3 *
      U * V * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U * T ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * U ^ 3 * τ ^
      2 * s ^ 3 * S ^ 2 + (-2) * u ^ 3 * U ^ 3 * V * τ * s ^ 3 * S ^ 2 + (-3) * u ^ 3 * U ^ 3 * V ^
      2 * s ^ 3 * S ^ 2 + (-4) * u ^ 3 * v ^ 2 * U * T * s ^ 3 * S ^ 2 + (-3) * u ^ 3 * v ^ 2 * U ^
      2 * τ * s ^ 3 * S ^ 2 + (-12) * u ^ 3 * v ^ 2 * U ^ 2 * V * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * v ^
      4 * U * s ^ 3 * S ^ 2 + (-2) * u ^ 4 * v * U ^ 2 * T * s ^ 3 * S ^ 2 + (-3) * u ^ 4 * v * U ^
      3 * τ * s ^ 3 * S ^ 2 + (-10) * u ^ 4 * v * U ^ 3 * V * s ^ 3 * S ^ 2 + (-4) * u ^ 4 * v ^ 3 *
      U ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 5 * U ^ 4 * τ * s ^ 3 * S ^ 2 + (-3) * u ^ 5 * U ^ 4 * V *
      s ^ 3 * S ^ 2 + (-6) * u ^ 5 * v ^ 2 * U ^ 3 * s ^ 3 * S ^ 2 + (-4) * u ^ 6 * v * U ^ 4 * s ^
      3 * S ^ 2 + (-1) * u ^ 7 * U ^ 5 * s ^ 3 * S ^ 2) * ht + ((-2) * v * V ^ 3 * s ^ 3 * S ^ 2 +
      (-1) * u * V ^ 2 * T * s ^ 3 * S ^ 2 + (-1) * u * U * V ^ 3 * s ^ 3 * S ^ 2 + (-7) * u * v ^ 2
      * V ^ 2 * s ^ 3 * S ^ 2 + (-1) * u ^ 2 * v * V * T * s ^ 3 * S ^ 2 + (-7) * u ^ 2 * v * U * V
      ^ 2 * s ^ 3 * S ^ 2 + (-7) * u ^ 2 * v ^ 3 * V * s ^ 3 * S ^ 2 + (-2) * u ^ 3 * U * V * T * s
      ^ 3 * S ^ 2 + (-3) * u ^ 3 * U ^ 2 * V ^ 2 * s ^ 3 * S ^ 2 + (-14) * u ^ 3 * v ^ 2 * U * V * s
      ^ 3 * S ^ 2 + (-2) * u ^ 3 * v ^ 4 * s ^ 3 * S ^ 2 + (-1) * u ^ 4 * v * U * T * s ^ 3 * S ^ 2
      + (-8) * u ^ 4 * v * U ^ 2 * V * s ^ 3 * S ^ 2 + (-7) * u ^ 4 * v ^ 3 * U * s ^ 3 * S ^ 2 +
      (-1) * u ^ 5 * U ^ 2 * T * s ^ 3 * S ^ 2 + (-3) * u ^ 5 * U ^ 3 * V * s ^ 3 * S ^ 2 + (-7) * u
      ^ 5 * v ^ 2 * U ^ 2 * s ^ 3 * S ^ 2 + (-3) * u ^ 6 * v * U ^ 3 * s ^ 3 * S ^ 2 + (-1) * u ^ 7
      * U ^ 4 * s ^ 3 * S ^ 2) * hT + ((-2) * v * U * V ^ 4 * s ^ 3 * S ^ 2 + (-2) * v ^ 3 * V ^ 3 *
      s ^ 3 * S ^ 2 + (-1) * u * U ^ 2 * V ^ 4 * s ^ 3 * S ^ 2 + (-8) * u * v ^ 2 * U * V ^ 3 * s ^
      3 * S ^ 2 + (-5) * u * v ^ 4 * V ^ 2 * s ^ 3 * S ^ 2 + (-10) * u ^ 2 * v * U ^ 2 * V ^ 3 * s ^
      3 * S ^ 2 + (-14) * u ^ 2 * v ^ 3 * U * V ^ 2 * s ^ 3 * S ^ 2 + (-4) * u ^ 2 * v ^ 5 * V * s ^
      3 * S ^ 2 + (-4) * u ^ 3 * U ^ 3 * V ^ 3 * s ^ 3 * S ^ 2 + (-25) * u ^ 3 * v ^ 2 * U ^ 2 * V ^
      2 * s ^ 3 * S ^ 2 + (-12) * u ^ 3 * v ^ 4 * U * V * s ^ 3 * S ^ 2 + (-1) * u ^ 3 * v ^ 6 * s ^
      3 * S ^ 2 + (-18) * u ^ 4 * v * U ^ 3 * V ^ 2 * s ^ 3 * S ^ 2 + (-22) * u ^ 4 * v ^ 3 * U ^ 2
      * V * s ^ 3 * S ^ 2 + (-4) * u ^ 4 * v ^ 5 * U * s ^ 3 * S ^ 2 + (-6) * u ^ 5 * U ^ 4 * V ^ 2
      * s ^ 3 * S ^ 2 + (-26) * u ^ 5 * v ^ 2 * U ^ 3 * V * s ^ 3 * S ^ 2 + (-7) * u ^ 5 * v ^ 4 * U
      ^ 2 * s ^ 3 * S ^ 2 + (-14) * u ^ 6 * v * U ^ 4 * V * s ^ 3 * S ^ 2 + (-10) * u ^ 6 * v ^ 3 *
      U ^ 3 * s ^ 3 * S ^ 2 + (-4) * u ^ 7 * U ^ 5 * V * s ^ 3 * S ^ 2 + (-9) * u ^ 7 * v ^ 2 * U ^
      4 * s ^ 3 * S ^ 2 + (-4) * u ^ 8 * v * U ^ 5 * s ^ 3 * S ^ 2 + (-1) * u ^ 9 * U ^ 6 * s ^ 3 *
      S ^ 2) * h2

theorem suzukiBruhat_entry_32 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    0 = v * V * T * s ^ 2 * S + v * U * τ * s * S + v ^ 3 * V * τ * s ^ 3 * S + u * T * s ^ 2 + u *
      U ^ 2 * τ * s * S + u * v ^ 2 * τ * s ^ 3 + u * v ^ 2 * U * V * τ * s ^ 3 * S + u ^ 2 * v * U
      * τ * s ^ 3 := by
  linear_combination (v * V * T ^ 2 * s ^ 2 * S ^ 2 + v * U * τ * T * s * S ^ 2 + v * U * τ ^ 2 * T
      * s ^ 2 * S ^ 2 + u * T ^ 2 * s ^ 2 * S + u * U ^ 2 * τ * T * s * S ^ 2 + u * U ^ 2 * τ ^ 2 *
      T * s ^ 2 * S ^ 2) * hts + (v * V * T * s ^ 2 * S + (-1) * v * V * τ * T * s ^ 3 * S + v * U *
      τ * s * S + (-1) * v * U * τ ^ 3 * s ^ 3 * S + u * T * s ^ 2 + u * U ^ 2 * τ * s * S + (-1) *
      u * U ^ 2 * τ ^ 3 * s ^ 3 * S + u * v ^ 2 * τ * s ^ 3 + u ^ 2 * v * U * τ * s ^ 3) * hTS +
      ((-1) * v * V * T * s ^ 3 * S + (-1) * v * U * τ ^ 2 * s ^ 3 * S + (-1) * v * U * V * τ * s ^
      3 * S + (-1) * v * U * V ^ 2 * s ^ 3 * S + (-1) * v ^ 3 * V * s ^ 3 * S + (-1) * u * T ^ 2 * s
      ^ 3 * S + (-1) * u * U ^ 2 * τ ^ 2 * s ^ 3 * S + (-1) * u * U ^ 2 * V * τ * s ^ 3 * S + (-1) *
      u * U ^ 2 * V ^ 2 * s ^ 3 * S + (-1) * u * v ^ 2 * T * s ^ 3 * S + (-1) * u * v ^ 2 * U * τ *
      s ^ 3 * S + (-3) * u * v ^ 2 * U * V * s ^ 3 * S + (-1) * u ^ 2 * v * U * T * s ^ 3 * S + (-2)
      * u ^ 2 * v * U ^ 2 * τ * s ^ 3 * S + (-4) * u ^ 2 * v * U ^ 2 * V * s ^ 3 * S + (-1) * u ^ 2
      * v ^ 3 * U * s ^ 3 * S + (-1) * u ^ 3 * U ^ 3 * τ * s ^ 3 * S + (-2) * u ^ 3 * U ^ 3 * V * s
      ^ 3 * S + (-3) * u ^ 3 * v ^ 2 * U ^ 2 * s ^ 3 * S + (-3) * u ^ 4 * v * U ^ 3 * s ^ 3 * S +
      (-1) * u ^ 5 * U ^ 4 * s ^ 3 * S) * ht + ((-1) * v * V ^ 2 * s ^ 3 * S + (-1) * u * V * T * s
      ^ 3 * S + (-1) * u * U * V ^ 2 * s ^ 3 * S + (-3) * u * v ^ 2 * V * s ^ 3 * S + (-1) * u ^ 2 *
      v * T * s ^ 3 * S + (-3) * u ^ 2 * v * U * V * s ^ 3 * S + (-2) * u ^ 2 * v ^ 3 * s ^ 3 * S +
      (-1) * u ^ 3 * U * T * s ^ 3 * S + (-2) * u ^ 3 * U ^ 2 * V * s ^ 3 * S + (-3) * u ^ 3 * v ^ 2
      * U * s ^ 3 * S + (-2) * u ^ 4 * v * U ^ 2 * s ^ 3 * S + (-1) * u ^ 5 * U ^ 3 * s ^ 3 * S) *
      hT + ((-1) * v * U * V ^ 3 * s ^ 3 * S + (-1) * v ^ 3 * V ^ 2 * s ^ 3 * S + (-1) * u * U ^ 2 *
      V ^ 3 * s ^ 3 * S + (-4) * u * v ^ 2 * U * V ^ 2 * s ^ 3 * S + (-2) * u * v ^ 4 * V * s ^ 3 *
      S + (-5) * u ^ 2 * v * U ^ 2 * V ^ 2 * s ^ 3 * S + (-5) * u ^ 2 * v ^ 3 * U * V * s ^ 3 * S +
      (-1) * u ^ 2 * v ^ 5 * s ^ 3 * S + (-3) * u ^ 3 * U ^ 3 * V ^ 2 * s ^ 3 * S + (-9) * u ^ 3 * v
      ^ 2 * U ^ 2 * V * s ^ 3 * S + (-2) * u ^ 3 * v ^ 4 * U * s ^ 3 * S + (-7) * u ^ 4 * v * U ^ 3
      * V * s ^ 3 * S + (-4) * u ^ 4 * v ^ 3 * U ^ 2 * s ^ 3 * S + (-3) * u ^ 5 * U ^ 4 * V * s ^ 3
      * S + (-5) * u ^ 5 * v ^ 2 * U ^ 3 * s ^ 3 * S + (-3) * u ^ 6 * v * U ^ 4 * s ^ 3 * S + (-1) *
      u ^ 7 * U ^ 5 * s ^ 3 * S) * h2

theorem suzukiBruhat_entry_33 {R : Type*} [CommRing R] (u v U V τ T s S : R)
    (hts : τ * s = 1) (hTS : T * S = 1) (ht : τ = U * u ^ 2 + u * v + V) (hT : T = U ^ 2 * u ^ 2 + U
    * V + v ^ 2) (h2 : (2 : R) = 0) :
    (1) = U * τ * S + v ^ 2 * V * τ * s ^ 2 * S + u * v * τ * s ^ 2 := by
  linear_combination ((-1) * T * S + (-1) * τ * T * s * S + U * τ * T * S ^ 2 + U * τ ^ 2 * T * s *
      S ^ 2) * hts + ((-1) + U * τ * S + (-1) * U * τ ^ 3 * s ^ 2 * S + u * v * τ * s ^ 2) * hTS +
      (τ * T * s ^ 2 * S + V * T * s ^ 2 * S + (-1) * U * τ ^ 2 * s ^ 2 * S + (-1) * U * V * τ * s ^
      2 * S + (-1) * U * V ^ 2 * s ^ 2 * S + (-1) * v ^ 2 * V * s ^ 2 * S + (-1) * u * v * U * τ * s
      ^ 2 * S + (-2) * u * v * U * V * s ^ 2 * S + u ^ 2 * U * T * s ^ 2 * S + (-1) * u ^ 2 * U ^ 2
      * τ * s ^ 2 * S + (-2) * u ^ 2 * U ^ 2 * V * s ^ 2 * S + (-1) * u ^ 2 * v ^ 2 * U * s ^ 2 * S
      + (-2) * u ^ 3 * v * U ^ 2 * s ^ 2 * S + (-1) * u ^ 4 * U ^ 3 * s ^ 2 * S) * ht + (V ^ 2 * s ^
      2 * S + u * v * V * s ^ 2 * S + (2) * u ^ 2 * U * V * s ^ 2 * S + u ^ 3 * v * U * s ^ 2 * S +
      u ^ 4 * U ^ 2 * s ^ 2 * S) * hT + ((-1) * u * v * U * V ^ 2 * s ^ 2 * S + (-1) * u ^ 2 * v ^ 2
      * U * V * s ^ 2 * S + (-2) * u ^ 3 * v * U ^ 2 * V * s ^ 2 * S + (-1) * u ^ 4 * v ^ 2 * U ^ 2
      * s ^ 2 * S + (-1) * u ^ 5 * v * U ^ 3 * s ^ 2 * S) * h2

theorem suzuki_bruhat_factorization [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K)
    (huv : (u, v) ≠ (0, 0)) :
    suzukiN a u v ≠ 0 ∧ ∀ t : Kˣ, (t : K) = suzukiN a u v →
      suzukiW K * suzukiS a u v * suzukiW K =
        suzukiS a (v / t) (u / t) * suzukiD a (t ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiW K *
          suzukiS a ((u ^ (2 ^ (a + 1) + 1) + v) / t) (v / (t : K) ^ 2 ^ (a + 1)) := by
  refine ⟨fun h => huv (Prod.ext ((suzuki_norm_nonzero a K hK u v).1 h).1
    ((suzuki_norm_nonzero a K hK u v).1 h).2), fun t htN => ?_⟩
  obtain ⟨h2, hadd, hθθ⟩ := suzuki_frob_data a hK
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hts : (t : K) * (t : K)⁻¹ = 1 := mul_inv_cancel₀ ht0
  have hTS : (t : K) ^ 2 ^ (a + 1) * ((t : K) ^ 2 ^ (a + 1))⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ ht0)
  have ht : (t : K) = u ^ 2 ^ (a + 1) * u ^ 2 + u * v + v ^ 2 ^ (a + 1) := by
    rw [htN, suzukiN, pow_add]
  have hT : (t : K) ^ 2 ^ (a + 1) =
      (u ^ 2 ^ (a + 1)) ^ 2 * u ^ 2 + u ^ 2 ^ (a + 1) * v ^ 2 ^ (a + 1) + v ^ 2 := by
    rw [ht, hadd, hadd, mul_pow, mul_pow, hθθ, hθθ, ← pow_mul, ← pow_mul, mul_comm 2, pow_mul]
    ring
  have hS0 := suzukiS_eq_explicit u v (u ^ 2 ^ (a + 1)) (v ^ 2 ^ (a + 1)) rfl rfl
  have hS1 := suzukiS_eq_explicit (a := a) (v * (t : K)⁻¹) (u * (t : K)⁻¹)
    (v ^ 2 ^ (a + 1) * ((t : K) ^ 2 ^ (a + 1))⁻¹) (u ^ 2 ^ (a + 1) * ((t : K) ^ 2 ^ (a + 1))⁻¹)
    (by rw [mul_pow, inv_pow]) (by rw [mul_pow, inv_pow])
  have hS2 := suzukiS_eq_explicit (a := a) ((u ^ 2 ^ (a + 1) * u + v) * (t : K)⁻¹)
    (v * ((t : K) ^ 2 ^ (a + 1))⁻¹)
    ((u ^ 2 ^ (a + 1) * u ^ 2 + v ^ 2 ^ (a + 1)) * ((t : K) ^ 2 ^ (a + 1))⁻¹)
    (v ^ 2 ^ (a + 1) * ((t : K)⁻¹) ^ 2)
    (by rw [mul_pow, hadd, mul_pow, hθθ, inv_pow]; ring)
    (by rw [mul_pow, inv_pow, hθθ, inv_pow])
  simp only [div_eq_mul_inv]
  rw [pow_succ u (2 ^ (a + 1)), hS0, hS1, hS2, suzukiD_two_sub_theta hK, suzukiW_eq]
  generalize ((t : K) ^ 2 ^ (a + 1))⁻¹ = S at hTS ⊢
  generalize (t : K) ^ 2 ^ (a + 1) = T at hTS hT ⊢
  generalize (t : K)⁻¹ = s at hts ⊢
  generalize u ^ 2 ^ (a + 1) = U at ht hT ⊢
  generalize v ^ 2 ^ (a + 1) = V at ht hT ⊢
  generalize (t : K) = τ at hts ht ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  · linear_combination suzukiBruhat_entry_00 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_01 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_02 u v U τ s hts
  · linear_combination suzukiBruhat_entry_03 u v U V τ ht
  · linear_combination suzukiBruhat_entry_10 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_11 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_12 u v U V τ T s hts ht hT h2
  · linear_combination suzukiBruhat_entry_13 v τ s hts
  · linear_combination suzukiBruhat_entry_20 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_21 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_22 u v U V τ T s S hts hTS ht
  · linear_combination suzukiBruhat_entry_23 u τ s hts
  · linear_combination suzukiBruhat_entry_30 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_31 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_32 u v U V τ T s S hts hTS ht hT h2
  · linear_combination suzukiBruhat_entry_33 u v U V τ T s S hts hTS ht hT h2

end CFSG.LieType.Ree
