module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

variable {G : Type*} [Group G]

theorem pow_mod_three {z : G} (hz : z ^ 3 = 1) (n : ℕ) : z ^ (n % 3) = z ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hz, one_pow, mul_one]

theorem pow_val_add {z : G} (hz : z ^ 3 = 1) (a b : ZMod 3) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [ZMod.val_add, pow_mod_three hz, pow_add]

theorem pow_val_mul {z : G} (hz : z ^ 3 = 1) (a b : ZMod 3) :
    z ^ (a * b).val = z ^ (a.val * b.val) := by
  rw [ZMod.val_mul, pow_mod_three hz]

theorem pow_mul_comm_of_mul {g h z : G} (hzg : Commute z g) {c : ℕ}
    (hgh : g * h = h * g * z ^ c) : ∀ m : ℕ, g ^ m * h = h * g ^ m * z ^ (m * c)
  | 0 => by simp
  | m + 1 => by
    have ih := pow_mul_comm_of_mul hzg hgh m
    have hzc : Commute (z ^ (m * c)) g := hzg.pow_left _
    calc g ^ (m + 1) * h = g ^ m * (g * h) := by rw [pow_succ, mul_assoc]
      _ = g ^ m * h * g * z ^ c := by rw [hgh]; simp only [mul_assoc]
      _ = h * g ^ m * (z ^ (m * c) * g) * z ^ c := by rw [ih]; simp only [mul_assoc]
      _ = h * g ^ (m + 1) * z ^ ((m + 1) * c) := by
        rw [hzc.eq, show (m + 1) * c = m * c + c by ring, pow_add z, pow_succ g]
        simp only [mul_assoc]

theorem pow_mul_pow_comm_of_mul {g h z : G} (hzg : Commute z g) (hzh : Commute z h) {c : ℕ}
    (hgh : g * h = h * g * z ^ c) (m : ℕ) :
    ∀ k : ℕ, g ^ m * h ^ k = h ^ k * g ^ m * z ^ (m * k * c)
  | 0 => by simp
  | k + 1 => by
    have ih := pow_mul_pow_comm_of_mul hzg hzh hgh m k
    have h1 := pow_mul_comm_of_mul hzg hgh m
    have hzc : Commute (z ^ (m * k * c)) h := hzh.pow_left _
    have e : m * (k + 1) * c = m * c + m * k * c := by ring
    calc g ^ m * h ^ (k + 1) = g ^ m * h ^ k * h := by rw [pow_succ, mul_assoc]
      _ = h ^ k * g ^ m * (z ^ (m * k * c) * h) := by rw [ih]; simp only [mul_assoc]
      _ = h ^ k * (g ^ m * h) * z ^ (m * k * c) := by rw [hzc.eq]; simp only [mul_assoc]
      _ = h ^ k * (h * g ^ m * z ^ (m * c)) * z ^ (m * k * c) := by rw [h1]
      _ = h ^ (k + 1) * g ^ m * z ^ (m * (k + 1) * c) := by
        rw [e, pow_add z, pow_succ]; simp only [mul_assoc]

theorem val_mul_mul (a b c : ZMod 3) : (a * b * c).val = a.val * b.val * c.val % 3 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

theorem pow_val_mul_pow_val {g h z : G} (hz : z ^ 3 = 1) (hzg : Commute z g)
    (hzh : Commute z h) {c : ZMod 3} (hgh : g * h = h * g * z ^ c.val) (a b : ZMod 3) :
    g ^ a.val * h ^ b.val = h ^ b.val * g ^ a.val * z ^ (a * b * c).val := by
  rw [pow_mul_pow_comm_of_mul hzg hzh hgh, val_mul_mul, pow_mod_three hz]

theorem pow_val_mul_pow_val_self {g : G} (hg : g ^ 3 = 1) (a b : ZMod 3) :
    g ^ a.val * g ^ b.val = g ^ (a + b).val :=
  (pow_val_add hg a b).symm

@[expose] def secN3 : (n : ℕ) → (Fin n → G) → (Fin n → ZMod 3) → G
  | 0, _, _ => 1
  | n + 1, s, v => s 0 ^ (v 0).val * secN3 n (fun i => s i.succ) (fun i => v i.succ)

@[expose] def betaN3 : (n : ℕ) → (Fin n → Fin n → ZMod 3) → (Fin n → ZMod 3) →
    (Fin n → ZMod 3) → ZMod 3
  | 0, _, _, _ => 0
  | n + 1, B, v, w => ∑ i : Fin n, v i.succ * w 0 * B i.succ 0 +
      betaN3 n (fun i j => B i.succ j.succ) (fun i => v i.succ) (fun i => w i.succ)

theorem secN3_eq_prod : ∀ (n : ℕ) (s : Fin n → G) (v : Fin n → ZMod 3),
    secN3 n s v = (List.ofFn fun i => s i ^ (v i).val).prod
  | 0, _, _ => rfl
  | n + 1, s, v => by
    rw [secN3, List.ofFn_succ, List.prod_cons, secN3_eq_prod n]

theorem commute_secN3 {z : G} : ∀ (n : ℕ) (s : Fin n → G) (v : Fin n → ZMod 3),
    (∀ i, Commute z (s i)) → Commute z (secN3 n s v)
  | 0, _, _, _ => Commute.one_right z
  | n + 1, _, _, h => ((h 0).pow_right _).mul_right (commute_secN3 n _ _ fun i => h i.succ)

private theorem mul_mul_comm_aux {a x t u c : G} (hx : x * t = t * x * c) (ha : a * t = t * a * u)
    (hu : Commute u x) : a * x * t = t * (a * x) * (u * c) := by
  calc a * x * t = a * (t * x * c) := by rw [mul_assoc, hx]
    _ = a * t * x * c := by simp only [mul_assoc]
    _ = t * a * (u * x) * c := by rw [ha]; simp only [mul_assoc]
    _ = t * (a * x) * (u * c) := by rw [hu.eq]; simp only [mul_assoc]

theorem secN3_mul_comm {z : G} (hz : z ^ 3 = 1) (t : G) :
    ∀ (n : ℕ) (s : Fin n → G) (v C : Fin n → ZMod 3), (∀ i, Commute z (s i)) →
      (∀ i, s i ^ (v i).val * t = t * s i ^ (v i).val * z ^ (C i).val) →
      secN3 n s v * t = t * secN3 n s v * z ^ (∑ i, C i).val
  | 0, _, _, _, _, _ => by simp [secN3]
  | n + 1, s, v, C, hzs, h => by
    rw [secN3, Fin.sum_univ_succ, pow_val_add hz]
    exact mul_mul_comm_aux (secN3_mul_comm hz t n _ _ (fun i => C i.succ) (fun i => hzs i.succ)
      fun i => h i.succ) (h 0) ((commute_secN3 n _ _ fun i => hzs i.succ).pow_left _)

private theorem assoc_aux {a x u t : G} : a * (x * u) * t = a * x * (u * t) := by
  simp only [mul_assoc]

private theorem mul_mul_mul_aux {a x b y c d u : G} (hx : x * b = b * x * u) (hu : Commute u y)
    (hab : a * b = c) (hxy : x * y = d) :
    a * x * (b * y) = c * d * u := by
  calc a * x * (b * y) = a * (x * b) * y := by simp only [mul_assoc]
    _ = a * b * x * (u * y) := by rw [hx]; simp only [mul_assoc]
    _ = a * b * (x * y) * u := by rw [hu.eq]; simp only [mul_assoc]
    _ = c * d * u := by rw [hab, hxy]

theorem secN3_mul_secN3 {z : G} (hz : z ^ 3 = 1) :
    ∀ (n : ℕ) (s : Fin n → G) (B : Fin n → Fin n → ZMod 3),
      (∀ i, Commute z (s i)) → (∀ i, s i ^ 3 = 1) →
      (∀ i j, s i * s j = s j * s i * z ^ (B i j).val) → ∀ v w : Fin n → ZMod 3,
      secN3 n s v * secN3 n s w = secN3 n s (v + w) * z ^ (betaN3 n B v w).val
  | 0, _, _, _, _, _, _, _ => by simp [secN3, betaN3]
  | n + 1, s, B, hzs, hcube, hcomm, v, w => by
    have hrec := secN3_mul_secN3 hz n (fun i => s i.succ) (fun i j => B i.succ j.succ)
      (fun i => hzs i.succ) (fun i => hcube i.succ) (fun i j => hcomm i.succ j.succ)
      (fun i => v i.succ) (fun i => w i.succ)
    have hmove := secN3_mul_comm hz (s 0 ^ (w 0).val) n (fun i => s i.succ) (fun i => v i.succ)
      (fun i => v i.succ * w 0 * B i.succ 0) (fun i => hzs i.succ)
      fun i => pow_val_mul_pow_val hz (hzs i.succ) (hzs 0) (hcomm i.succ 0) _ _
    have hu : Commute (z ^ (∑ i : Fin n, v i.succ * w 0 * B i.succ 0).val)
        (secN3 n (fun i => s i.succ) fun i => w i.succ) :=
      (commute_secN3 n _ _ fun i => hzs i.succ).pow_left _
    have e := mul_mul_mul_aux hmove hu (pow_val_mul_pow_val_self (hcube 0) (v 0) (w 0)) hrec
    rw [secN3, secN3, secN3, betaN3, e, assoc_aux, ← pow_val_add hz,
      add_comm (betaN3 n (fun i j => B i.succ j.succ) (fun i => v i.succ) (fun i => w i.succ))]
    rfl

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
