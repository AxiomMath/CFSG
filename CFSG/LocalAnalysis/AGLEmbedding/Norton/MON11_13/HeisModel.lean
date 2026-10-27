module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.AGLEmbedding.Norton.MON11_13.HeisModel

abbrev T := ZMod 13 × ZMod 13 × ZMod 13

@[expose] def mul (u v : T) : T := (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2 + 4 * u.2.1 * v.1)

@[expose] def pw (u : T) : ℕ → T
  | 0 => (0, 0, 0)
  | n + 1 => mul (pw u n) u

abbrev Aff := T × T × T

@[expose] def act (A : Aff) (u : T) : T :=
  mul (mul (pw A.1 u.1.val) (pw A.2.1 u.2.1.val)) (pw A.2.2 u.2.2.val)

@[expose] def comp (A B : Aff) : Aff := (act A B.1, act A B.2.1, act A B.2.2)

@[expose] def apow (A : Aff) : ℕ → Aff
  | 0 => ((1, 0, 0), (0, 1, 0), (0, 0, 1))
  | n + 1 => comp (apow A n) A

variable {G : Type*} [Group G] {x y z : G}

structure Heis (x y z : G) : Prop where
  x13 : x ^ 13 = 1
  y13 : y ^ 13 = 1
  z13 : z ^ 13 = 1
  zx : Commute z x
  zy : Commute z y
  yx : y * x = x * (y * z ^ 4)

@[expose] def ev (x y z : G) (u : T) : G := x ^ u.1.val * y ^ u.2.1.val * z ^ u.2.2.val

theorem pow_val {g : G} (h : g ^ 13 = 1) (n : ℕ) : g ^ (n : ZMod 13).val = g ^ n := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n 13, pow_add, pow_mul, h, one_pow, mul_one]

theorem eq_pow_four_pow {g : G} (h : g ^ 13 = 1) : g = (g ^ 4) ^ 10 := by
  have e : 4 * 10 = 13 * 3 + 1 := rfl
  rw [← pow_mul, e, pow_add, pow_mul, h, one_pow, one_mul, pow_one]

namespace Heis

variable (H : Heis x y z)
include H

theorem ev_nat (a b c : ℕ) : ev x y z ((a : ZMod 13), (b : ZMod 13), (c : ZMod 13)) =
    x ^ a * y ^ b * z ^ c := by
  unfold ev
  rw [pow_val H.x13, pow_val H.y13, pow_val H.z13]

theorem ev_x (a : ℕ) : ev x y z ((a : ZMod 13), 0, 0) = x ^ a := by
  have := H.ev_nat a 0 0
  rwa [Nat.cast_zero, pow_zero, pow_zero, mul_one, mul_one] at this

theorem ev_y (b : ℕ) : ev x y z (0, (b : ZMod 13), 0) = y ^ b := by
  have := H.ev_nat 0 b 0
  rwa [Nat.cast_zero, pow_zero, pow_zero, mul_one, one_mul] at this

theorem ev_z (c : ℕ) : ev x y z (0, 0, (c : ZMod 13)) = z ^ c := by
  have := H.ev_nat 0 0 c
  rwa [Nat.cast_zero, pow_zero, pow_zero, one_mul, one_mul] at this

theorem ev_xy (a b : ℕ) : ev x y z ((a : ZMod 13), (b : ZMod 13), 0) = x ^ a * y ^ b := by
  have := H.ev_nat a b 0
  rwa [Nat.cast_zero, pow_zero, mul_one] at this

theorem ev_zero : ev x y z (0, 0, 0) = 1 := by
  have := H.ev_nat 0 0 0
  rwa [Nat.cast_zero, pow_zero, pow_zero, pow_zero, one_mul, one_mul] at this

theorem ev_one_x : ev x y z (1, 0, 0) = x := by
  have := H.ev_x 1
  rwa [Nat.cast_one, pow_one] at this

theorem ev_one_y : ev x y z (0, 1, 0) = y := by
  have := H.ev_y 1
  rwa [Nat.cast_one, pow_one] at this

theorem ev_one_z : ev x y z (0, 0, 1) = z := by
  have := H.ev_z 1
  rwa [Nat.cast_one, pow_one] at this

theorem y_mul_xpow (a : ℕ) : y * x ^ a = x ^ a * y * z ^ (4 * a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hzx : z ^ (4 * a) * x = x * z ^ (4 * a) := (H.zx.pow_left (4 * a)).eq
    have e : 4 * (a + 1) = 4 + 4 * a := by omega
    calc y * x ^ (a + 1) = y * x ^ a * x := by rw [pow_succ x a, mul_assoc]
      _ = x ^ a * y * (z ^ (4 * a) * x) := by rw [ih, mul_assoc]
      _ = x ^ a * (y * x) * z ^ (4 * a) := by rw [hzx]; simp only [mul_assoc]
      _ = x ^ (a + 1) * y * z ^ (4 * (a + 1)) := by
        rw [H.yx, pow_succ x a, e, pow_add]
        simp only [mul_assoc]

theorem ypow_mul_xpow (b a : ℕ) : y ^ b * x ^ a = x ^ a * y ^ b * z ^ (4 * b * a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hzy : z ^ (4 * b * a) * y = y * z ^ (4 * b * a) := (H.zy.pow_left (4 * b * a)).eq
    have e : 4 * (b + 1) * a = 4 * b * a + 4 * a := by ring
    calc y ^ (b + 1) * x ^ a = y ^ b * (y * x ^ a) := by rw [pow_succ y b, mul_assoc]
      _ = (y ^ b * x ^ a) * y * z ^ (4 * a) := by rw [H.y_mul_xpow]; simp only [mul_assoc]
      _ = x ^ a * y ^ b * (z ^ (4 * b * a) * y) * z ^ (4 * a) := by rw [ih]; simp only [mul_assoc]
      _ = x ^ a * y ^ (b + 1) * z ^ (4 * (b + 1) * a) := by
        rw [hzy, pow_succ y b, e, pow_add]
        simp only [mul_assoc]

theorem nf_mul (a b c a' b' c' : ℕ) :
    x ^ a * y ^ b * z ^ c * (x ^ a' * y ^ b' * z ^ c') =
      x ^ (a + a') * y ^ (b + b') * z ^ (c + c' + 4 * b * a') := by
  have h1 : z ^ c * x ^ a' = x ^ a' * z ^ c := (H.zx.pow_pow c a').eq
  have h2 : z ^ c * y ^ b' = y ^ b' * z ^ c := (H.zy.pow_pow c b').eq
  have h3 : z ^ (4 * b * a') * y ^ b' = y ^ b' * z ^ (4 * b * a') :=
    (H.zy.pow_pow (4 * b * a') b').eq
  have e : c + c' + 4 * b * a' = 4 * b * a' + c + c' := by ring
  calc x ^ a * y ^ b * z ^ c * (x ^ a' * y ^ b' * z ^ c')
      = x ^ a * y ^ b * (z ^ c * x ^ a') * y ^ b' * z ^ c' := by simp only [mul_assoc]
    _ = x ^ a * (y ^ b * x ^ a') * (z ^ c * y ^ b') * z ^ c' := by
        rw [h1]; simp only [mul_assoc]
    _ = x ^ a * x ^ a' * (y ^ b * (z ^ (4 * b * a') * y ^ b')) * z ^ c * z ^ c' := by
        rw [H.ypow_mul_xpow, h2]; simp only [mul_assoc]
    _ = x ^ (a + a') * y ^ (b + b') * z ^ (c + c' + 4 * b * a') := by
        rw [h3, e]
        simp only [pow_add, mul_assoc]

theorem ev_mul (u v : T) : ev x y z u * ev x y z v = ev x y z (mul u v) := by
  have e : mul u v = (((u.1.val + v.1.val : ℕ) : ZMod 13), ((u.2.1.val + v.2.1.val : ℕ) : ZMod 13),
      ((u.2.2.val + v.2.2.val + 4 * u.2.1.val * v.1.val : ℕ) : ZMod 13)) := by
    simp only [mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_val, ZMod.cast_id', id]
  rw [e, H.ev_nat]
  exact H.nf_mul _ _ _ _ _ _

theorem ev_pw (u : T) (n : ℕ) : ev x y z u ^ n = ev x y z (pw u n) := by
  induction n with
  | zero => rw [pow_zero, pw, H.ev_zero]
  | succ n ih => rw [pow_succ, ih, H.ev_mul, pw]

theorem ev_mul_x (u : T) : ev x y z u * x = ev x y z (mul u (1, 0, 0)) := by
  rw [← H.ev_mul, H.ev_one_x]

theorem x_mul_ev (u : T) : x * ev x y z u = ev x y z (mul (1, 0, 0) u) := by
  rw [← H.ev_mul, H.ev_one_x]

theorem ev_mul_y (u : T) : ev x y z u * y = ev x y z (mul u (0, 1, 0)) := by
  rw [← H.ev_mul, H.ev_one_y]

theorem y_mul_ev (u : T) : y * ev x y z u = ev x y z (mul (0, 1, 0) u) := by
  rw [← H.ev_mul, H.ev_one_y]

theorem ev_mul_z (u : T) : ev x y z u * z = ev x y z (mul u (0, 0, 1)) := by
  rw [← H.ev_mul, H.ev_one_z]

theorem z_mul_ev (u : T) : z * ev x y z u = ev x y z (mul (0, 0, 1) u) := by
  rw [← H.ev_mul, H.ev_one_z]

theorem conj_ev_of_mul {w u v : T} (e : mul w u = mul v w) :
    ev x y z w * ev x y z u * (ev x y z w)⁻¹ = ev x y z v := by
  rw [mul_inv_eq_iff_eq_mul, H.ev_mul, H.ev_mul, e]

end Heis

structure Acts (x y z g : G) (A : Aff) : Prop where
  ax : g * x * g⁻¹ = ev x y z A.1
  ay : g * y * g⁻¹ = ev x y z A.2.1
  az : g * z * g⁻¹ = ev x y z A.2.2

namespace Acts

variable {g h : G} {A B : Aff}

theorem one (H : Heis x y z) : Acts x y z 1 ((1, 0, 0), (0, 1, 0), (0, 0, 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [one_mul, inv_one, mul_one, H.ev_one_x, H.ev_one_y, H.ev_one_z]

theorem conj_ev (H : Heis x y z) (hA : Acts x y z g A) (u : T) :
    g * ev x y z u * g⁻¹ = ev x y z (act A u) := by
  have e : ∀ w : G, g * w * g⁻¹ = MulAut.conj g w := fun w => (MulAut.conj_apply g w).symm
  have hu : ev x y z u = x ^ u.1.val * y ^ u.2.1.val * z ^ u.2.2.val := rfl
  rw [e, hu, map_mul, map_mul, map_pow, map_pow, map_pow, ← e, ← e, ← e, hA.ax, hA.ay, hA.az,
    H.ev_pw, H.ev_pw, H.ev_pw, H.ev_mul, H.ev_mul]
  rfl

theorem mul (H : Heis x y z) (hA : Acts x y z g A) (hB : Acts x y z h B) :
    Acts x y z (g * h) (comp A B) := by
  have e : ∀ w : G, g * h * w * (g * h)⁻¹ = g * (h * w * h⁻¹) * g⁻¹ := fun w => by
    simp only [mul_inv_rev, mul_assoc]
  exact ⟨by rw [e, hB.ax, hA.conj_ev H]; rfl, by rw [e, hB.ay, hA.conj_ev H]; rfl,
    by rw [e, hB.az, hA.conj_ev H]; rfl⟩

theorem pow (H : Heis x y z) (hA : Acts x y z g A) (n : ℕ) : Acts x y z (g ^ n) (apow A n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [pow_zero, one_mul, inv_one, mul_one, apow, H.ev_one_x, H.ev_one_y, H.ev_one_z]
  | succ n ih => rw [pow_succ]; exact ih.mul H hA

end Acts

theorem acts_of (H : Heis x y z) {g : G} {p q r : T} (hp : g * x * g⁻¹ = ev x y z p)
    (hq : g * y * g⁻¹ = ev x y z q) (hr : mul (mul p q) (pw r 4) = mul q p)
    (hr13 : pw r 13 = (0, 0, 0)) : Acts x y z g (p, q, r) := by
  refine ⟨hp, hq, ?_⟩
  have e : ∀ w : G, g * w * g⁻¹ = MulAut.conj g w := fun w => (MulAut.conj_apply g w).symm
  set w := g * z * g⁻¹ with hw
  have hrel : ev x y z q * ev x y z p = ev x y z p * ev x y z q * w ^ 4 := by
    rw [← hp, ← hq, hw, e, e, e, ← map_mul, ← map_pow, ← map_mul, ← map_mul, H.yx, mul_assoc]
  have hmod : ev x y z q * ev x y z p = ev x y z p * ev x y z q * ev x y z r ^ 4 := by
    rw [H.ev_mul, H.ev_mul, H.ev_pw, H.ev_mul, hr]
  have h4 : w ^ 4 = ev x y z r ^ 4 := mul_left_cancel (hrel.symm.trans hmod)
  have hw13 : w ^ 13 = 1 := by rw [hw, e, ← map_pow, H.z13, map_one]
  have hr13' : ev x y z r ^ 13 = 1 := by rw [H.ev_pw, hr13, H.ev_zero]
  rw [eq_pow_four_pow hw13, h4, ← eq_pow_four_pow hr13']

theorem acts_ev (H : Heis x y z) {w : T} {A : Aff} (h1 : mul w (1, 0, 0) = mul A.1 w)
    (h2 : mul w (0, 1, 0) = mul A.2.1 w) (h3 : mul w (0, 0, 1) = mul A.2.2 w) :
    Acts x y z (ev x y z w) A := by
  have e1 := H.conj_ev_of_mul h1
  have e2 := H.conj_ev_of_mul h2
  have e3 := H.conj_ev_of_mul h3
  rw [H.ev_one_x] at e1
  rw [H.ev_one_y] at e2
  rw [H.ev_one_z] at e3
  exact ⟨e1, e2, e3⟩

end CFSG.AGLEmbedding.Norton.MON11_13.HeisModel

end
