module

public import CFSG.LargeExtraspecial.FS77Core
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.LargeExtraspecial.FS77

variable {G : Type*} [Group G]

namespace NF

theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

theorem zmod2_one_add_one : (1 + 1 : ZMod 2) = 0 := rfl

theorem pow_val_add {z : G} (hz : z * z = 1) (a b : ZMod 2) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rcases Core.zmod2_cases a with rfl | rfl <;> rcases Core.zmod2_cases b with rfl | rfl <;>
    simp [zmod2_val_one, zmod2_one_add_one, hz]

theorem pow_val_mul_pow_val {g h z : G} {c : ZMod 2} (hgh : g * h = h * g * z ^ c.val)
    (a b : ZMod 2) : g ^ a.val * h ^ b.val = h ^ b.val * g ^ a.val * z ^ (a * b * c).val := by
  rcases Core.zmod2_cases a with rfl | rfl <;> rcases Core.zmod2_cases b with rfl | rfl <;>
    simp [zmod2_val_one, hgh]

theorem pow_val_mul_pow_val_self {g z : G} {q : ZMod 2} (hg : g * g = z ^ q.val) (a b : ZMod 2) :
    g ^ a.val * g ^ b.val = g ^ (a + b).val * z ^ (a * b * q).val := by
  rcases Core.zmod2_cases a with rfl | rfl <;> rcases Core.zmod2_cases b with rfl | rfl <;>
    simp [zmod2_val_one, zmod2_one_add_one, hg]

@[expose] def secN : (n : ℕ) → (Fin n → G) → (Fin n → ZMod 2) → G
  | 0, _, _ => 1
  | n + 1, s, v => s 0 ^ (v 0).val * secN n (fun i => s i.succ) (fun i => v i.succ)

@[expose] def betaN : (n : ℕ) → (Fin n → ZMod 2) → (Fin n → Fin n → ZMod 2) →
    (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2
  | 0, _, _, _, _ => 0
  | n + 1, q, B, v, w => v 0 * w 0 * q 0 + ∑ i : Fin n, v i.succ * w 0 * B i.succ 0 +
      betaN n (fun i => q i.succ) (fun i j => B i.succ j.succ) (fun i => v i.succ)
        (fun i => w i.succ)

theorem commute_secN {z : G} : ∀ (n : ℕ) (s : Fin n → G) (v : Fin n → ZMod 2),
    (∀ i, Commute z (s i)) → Commute z (secN n s v)
  | 0, _, _, _ => Commute.one_right z
  | n + 1, _, _, h => ((h 0).pow_right _).mul_right (commute_secN n _ _ fun i => h i.succ)

private theorem mul_mul_comm_aux {a x t u c : G} (hx : x * t = t * x * c) (ha : a * t = t * a * u)
    (hu : Commute u x) : a * x * t = t * (a * x) * (u * c) := by
  calc a * x * t = a * (t * x * c) := by rw [mul_assoc, hx]
    _ = a * t * x * c := by simp only [mul_assoc]
    _ = t * a * (u * x) * c := by rw [ha]; simp only [mul_assoc]
    _ = t * (a * x) * (u * c) := by rw [hu.eq]; simp only [mul_assoc]

theorem secN_mul_comm {z : G} (hz : z * z = 1) (t : G) :
    ∀ (n : ℕ) (s : Fin n → G) (v C : Fin n → ZMod 2), (∀ i, Commute z (s i)) →
      (∀ i, s i ^ (v i).val * t = t * s i ^ (v i).val * z ^ (C i).val) →
      secN n s v * t = t * secN n s v * z ^ (∑ i, C i).val
  | 0, _, _, _, _, _ => by simp [secN]
  | n + 1, s, v, C, hzs, h => by
    rw [secN, Fin.sum_univ_succ, pow_val_add hz]
    exact mul_mul_comm_aux (secN_mul_comm hz t n _ _ (fun i => C i.succ) (fun i => hzs i.succ)
      fun i => h i.succ) (h 0) ((commute_secN n _ _ fun i => hzs i.succ).pow_left _)

private theorem mul_mul_mul_aux {a x b y c d e u f : G} (hx : x * b = b * x * u) (hu : Commute u y)
    (hab : a * b = c * e) (hxy : x * y = d * f) (he : Commute e d) (huf : Commute u f) :
    a * x * (b * y) = c * d * (e * u * f) := by
  calc a * x * (b * y) = a * (x * b) * y := by simp only [mul_assoc]
    _ = a * b * x * (u * y) := by rw [hx]; simp only [mul_assoc]
    _ = a * b * (x * y) * u := by rw [hu.eq]; simp only [mul_assoc]
    _ = c * (e * d) * f * u := by rw [hab, hxy]; simp only [mul_assoc]
    _ = c * d * (e * u * f) := by rw [he.eq]; simp only [mul_assoc]; rw [huf.eq]

theorem secN_mul_secN {z : G} (hz : z * z = 1) :
    ∀ (n : ℕ) (s : Fin n → G) (q : Fin n → ZMod 2) (B : Fin n → Fin n → ZMod 2),
      (∀ i, Commute z (s i)) → (∀ i, s i * s i = z ^ (q i).val) →
      (∀ i j, s i * s j = s j * s i * z ^ (B i j).val) → ∀ v w : Fin n → ZMod 2,
      secN n s v * secN n s w = secN n s (v + w) * z ^ (betaN n q B v w).val
  | 0, _, _, _, _, _, _, _, _ => by simp [secN, betaN]
  | n + 1, s, q, B, hzs, hsq, hcomm, v, w => by
    have hc : ∀ (u : Fin n → ZMod 2) (a : ZMod 2),
        Commute (z ^ a.val) (secN n (fun i => s i.succ) u) := fun u _ =>
      (commute_secN n _ u fun i => hzs i.succ).pow_left _
    rw [secN, secN, secN, betaN, pow_val_add hz, pow_val_add hz]
    exact mul_mul_mul_aux
      (secN_mul_comm hz _ n _ _ (fun i => v i.succ * w 0 * B i.succ 0) (fun i => hzs i.succ)
        fun i => pow_val_mul_pow_val (hcomm i.succ 0) _ _)
      (hc _ _) (pow_val_mul_pow_val_self (hsq 0) _ _)
      (secN_mul_secN hz n _ (fun i => q i.succ) (fun i j => B i.succ j.succ)
        (fun i => hzs i.succ) (fun i => hsq i.succ) (fun i j => hcomm i.succ j.succ) _ _)
      (hc _ _) (Commute.pow_pow_self z _ _)

end NF

@[expose] def qv6 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 1]

@[expose] def Bm6 : Fin 6 → Fin 6 → ZMod 2 := fun i j => polar6 (Pi.single i 1) (Pi.single j 1)

@[expose] def sec (s : Fin 6 → G) (v : V6) : G :=
  s 0 ^ (v 0).val * s 1 ^ (v 1).val * s 2 ^ (v 2).val * s 3 ^ (v 3).val * s 4 ^ (v 4).val *
    s 5 ^ (v 5).val

namespace NF

theorem sec_eq_secN (s : Fin 6 → G) (v : V6) : sec s v = secN 6 s v := by
  simp only [sec, secN, mul_assoc, mul_one]
  rfl

theorem betaN_six (v w : V6) : betaN 6 qv6 Bm6 v w = beta6 v w := by
  simp [betaN, Fin.sum_univ_succ, qv6, Bm6, polar6, beta6]
  ring

end NF

theorem sec_mul_sec {z : G} (hz : z * z = 1) {s : Fin 6 → G}
    (hzs : ∀ i, z * s i = s i * z) (hsq : ∀ i, s i * s i = z ^ (qv6 i).val)
    (hcomm : ∀ i j, s i * s j = s j * s i * z ^ (Bm6 i j).val) (v w : V6) :
    sec s v * sec s w = sec s (v + w) * z ^ (beta6 v w).val := by
  rw [NF.sec_eq_secN, NF.sec_eq_secN, NF.sec_eq_secN, ← NF.betaN_six]
  exact NF.secN_mul_secN hz 6 s qv6 Bm6 hzs hsq hcomm v w

end CFSG.LargeExtraspecial.FS77
