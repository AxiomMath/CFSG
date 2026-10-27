module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open scoped commutatorElement

@[ext] structure Heis (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p

namespace Heis

variable {p : ℕ}

instance : One (Heis p) := ⟨⟨0, 0, 0⟩⟩
instance : Mul (Heis p) := ⟨fun u v => ⟨u.a + v.a, u.b + v.b, u.c + v.c - v.a * u.b⟩⟩
instance : Inv (Heis p) := ⟨fun u => ⟨-u.a, -u.b, -u.c - u.a * u.b⟩⟩

@[simp] lemma one_a : (1 : Heis p).a = 0 := rfl
@[simp] lemma one_b : (1 : Heis p).b = 0 := rfl
@[simp] lemma one_c : (1 : Heis p).c = 0 := rfl
@[simp] lemma mul_a (u v : Heis p) : (u * v).a = u.a + v.a := rfl
@[simp] lemma mul_b (u v : Heis p) : (u * v).b = u.b + v.b := rfl
@[simp] lemma mul_c (u v : Heis p) : (u * v).c = u.c + v.c - v.a * u.b := rfl
@[simp] lemma inv_a (u : Heis p) : (u⁻¹).a = -u.a := rfl
@[simp] lemma inv_b (u : Heis p) : (u⁻¹).b = -u.b := rfl
@[simp] lemma inv_c (u : Heis p) : (u⁻¹).c = -u.c - u.a * u.b := rfl

instance : Group (Heis p) where
  mul_assoc u v w := by ext <;> simp <;> ring
  one_mul u := by ext <;> simp
  mul_one u := by ext <;> simp
  inv_mul_cancel u := by ext <;> simp <;> ring

@[expose] def X : Heis p := ⟨1, 0, 0⟩
@[expose] def Y : Heis p := ⟨0, 1, 0⟩
@[expose] def Zc : Heis p := ⟨0, 0, 1⟩

theorem card_heis [NeZero p] : Nat.card (Heis p) = p ^ 3 := by
  let e : Heis p ≃ ZMod p × ZMod p × ZMod p :=
    { toFun := fun u => (u.a, u.b, u.c)
      invFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun t => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

theorem comm_eq (u v : Heis p) : ⁅u, v⁆ = ⟨0, 0, u.a * v.b - u.b * v.a⟩ := by
  ext <;> simp only [commutatorElement_def, mul_a, mul_b, mul_c, inv_a, inv_b, inv_c] <;> ring

theorem pow_eq (u : Heis p) (n : ℕ) :
    u ^ n = ⟨n * u.a, n * u.b, n * u.c - (n.choose 2 : ZMod p) * (u.a * u.b)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
    have h2 : (k + 1).choose 2 = k + k.choose 2 := by
      simp [Nat.choose_succ_succ]
    rw [pow_succ, ih]
    ext
    · simp only [mul_a]
      push_cast
      ring
    · simp only [mul_b]
      push_cast
      ring
    · simp only [mul_c, h2]
      push_cast
      ring

theorem pow_prime [Fact p.Prime] (hp : p ≠ 2) (u : Heis p) : u ^ p = 1 := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpd : p ∣ p.choose 2 := (Fact.out : p.Prime).dvd_choose_self (by norm_num) (by omega)
  have hz : ((p.choose 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpd
  rw [pow_eq]
  ext
  · simp
  · simp
  · simp [hz]

theorem closure_XY [NeZero p] : Subgroup.closure ({X, Y} : Set (Heis p)) = ⊤ := by
  have hX : (X : Heis p) ∈ Subgroup.closure ({X, Y} : Set (Heis p)) :=
    Subgroup.subset_closure (by simp)
  have hY : (Y : Heis p) ∈ Subgroup.closure ({X, Y} : Set (Heis p)) :=
    Subgroup.subset_closure (by simp)
  have hZ : (Zc : Heis p) ∈ Subgroup.closure ({X, Y} : Set (Heis p)) := by
    have hc : ⁅(X : Heis p), (Y : Heis p)⁆ = Zc := by
      rw [comm_eq]
      ext <;> simp [X, Y, Zc]
    rw [← hc, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hX hY) (Subgroup.inv_mem _ hX))
      (Subgroup.inv_mem _ hY)
  have hXn : ∀ n : ℕ, (X : Heis p) ^ n = ⟨(n : ZMod p), 0, 0⟩ := by
    intro n
    rw [pow_eq]
    ext <;> simp [X]
  have hYn : ∀ n : ℕ, (Y : Heis p) ^ n = ⟨0, (n : ZMod p), 0⟩ := by
    intro n
    rw [pow_eq]
    ext <;> simp [Y]
  have hZn : ∀ n : ℕ, (Zc : Heis p) ^ n = ⟨0, 0, (n : ZMod p)⟩ := by
    intro n
    rw [pow_eq]
    ext <;> simp [Zc]
  rw [eq_top_iff]
  intro u _
  have hu : u = X ^ u.a.val * Y ^ u.b.val * Zc ^ u.c.val := by
    rw [hXn, hYn, hZn]
    ext <;> simp
  rw [hu]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hX _) (Subgroup.pow_mem _ hY _))
    (Subgroup.pow_mem _ hZ _)

@[expose] def Mline (v : ZMod p × ZMod p) : Subgroup (Heis p) where
  carrier := {h | h.a * v.2 = h.b * v.1}
  one_mem' := by simp
  mul_mem' := by
    intro u w hu hw
    simp only [Set.mem_setOf_eq, mul_a, mul_b] at *
    rw [add_mul, add_mul, hu, hw]
  inv_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq, inv_a, inv_b] at *
    rw [neg_mul, neg_mul, hu]

theorem Mline_card [Fact p.Prime] {v : ZMod p × ZMod p} (hv : v ≠ 0) :
    Nat.card (Mline v) = p ^ 2 := by
  have hv' : v.1 = 0 → v.2 ≠ 0 := fun h1 h2 => hv (Prod.ext h1 h2)
  have hmem : ∀ q : ZMod p × ZMod p, (⟨q.1 * v.1, q.1 * v.2, q.2⟩ : Heis p) ∈ Mline v := by
    intro q
    show q.1 * v.1 * v.2 = q.1 * v.2 * v.1
    ring
  let e : ZMod p × ZMod p ≃ Mline v :=
    { toFun := fun q => ⟨⟨q.1 * v.1, q.1 * v.2, q.2⟩, hmem q⟩
      invFun := fun h =>
        ((if v.1 = 0 then (h : Heis p).b / v.2 else (h : Heis p).a / v.1), (h : Heis p).c)
      left_inv := by
        intro q
        by_cases h1 : v.1 = 0
        · have h2 := hv' h1
          show ((if v.1 = 0 then q.1 * v.2 / v.2 else q.1 * v.1 / v.1), q.2) = q
          rw [if_pos h1, mul_div_cancel_right₀ _ h2]
        · show ((if v.1 = 0 then q.1 * v.2 / v.2 else q.1 * v.1 / v.1), q.2) = q
          rw [if_neg h1, mul_div_cancel_right₀ _ h1]
      right_inv := by
        rintro ⟨⟨a, b, c⟩, hh⟩
        have hh' : a * v.2 = b * v.1 := hh
        apply Subtype.ext
        apply Heis.ext
        · by_cases h1 : v.1 = 0
          · have h2 := hv' h1
            have ha : a = 0 := by
              have h3 : a * v.2 = 0 := by rw [hh', h1, mul_zero]
              exact (mul_eq_zero.mp h3).resolve_right h2
            show (if v.1 = 0 then b / v.2 else a / v.1) * v.1 = a
            rw [if_pos h1, h1, ha, mul_zero]
          · show (if v.1 = 0 then b / v.2 else a / v.1) * v.1 = a
            rw [if_neg h1, div_mul_cancel₀ a h1]
        · by_cases h1 : v.1 = 0
          · have h2 := hv' h1
            show (if v.1 = 0 then b / v.2 else a / v.1) * v.2 = b
            rw [if_pos h1, div_mul_cancel₀ b h2]
          · show (if v.1 = 0 then b / v.2 else a / v.1) * v.2 = b
            rw [if_neg h1]
            calc a / v.1 * v.2 = a * v.2 / v.1 := by ring
              _ = b * v.1 / v.1 := by rw [hh']
              _ = b := mul_div_cancel_right₀ b h1
        · rfl }
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod, sq]

theorem Mline_smul [Fact p.Prime] {v : ZMod p × ZMod p} {s : ZMod p} (hs : s ≠ 0) :
    Mline (s * v.1, s * v.2) = Mline v := by
  ext h
  show h.a * (s * v.2) = h.b * (s * v.1) ↔ h.a * v.2 = h.b * v.1
  constructor
  · intro H
    apply mul_left_cancel₀ hs
    linear_combination H
  · intro H
    linear_combination s * H

theorem exists_Mline [Fact p.Prime] (hp : p ≠ 2) (M : Subgroup (Heis p)) (hM : Nat.card M = p ^ 2) :
    ∃ v : ZMod p × ZMod p, v ≠ 0 ∧ M = Mline v := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : Finite (Heis p) :=
    Finite.of_injective (fun h : Heis p => (h.a, h.b, h.c)) (by
      intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact Heis.ext hxy.1 hxy.2.1 hxy.2.2)
  have hcomm : ∀ x y : M, x * y = y * x :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hM).is_comm.comm
  obtain ⟨m, hmM, hm⟩ : ∃ m : Heis p, m ∈ M ∧ (m.a ≠ 0 ∨ m.b ≠ 0) := by
    by_contra hcon
    simp only [not_exists, not_and, not_or, ne_eq, not_not] at hcon
    have hinj : Function.Injective (fun x : M => (x : Heis p).c) := by
      intro x y hxy
      apply Subtype.ext
      apply Heis.ext
      · rw [(hcon (x : Heis p) x.2).1, (hcon (y : Heis p) y.2).1]
      · rw [(hcon (x : Heis p) x.2).2, (hcon (y : Heis p) y.2).2]
      · exact hxy
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hM, Nat.card_zmod] at hle
    have hp2 := hpp.two_le
    nlinarith
  have hv0 : (m.a, m.b) ≠ 0 := by
    intro h0
    have h1 : m.a = 0 := congrArg Prod.fst h0
    have h2 : m.b = 0 := congrArg Prod.snd h0
    rcases hm with h | h
    · exact h h1
    · exact h h2
  refine ⟨(m.a, m.b), hv0, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    have hc : (m * x).c = (x * m).c :=
      congrArg (fun y : M => (y : Heis p).c) (hcomm ⟨m, hmM⟩ ⟨x, hx⟩)
    rw [mul_c, mul_c] at hc
    show x.a * m.b = x.b * m.a
    linear_combination -hc
  · exact (Mline_card hv0).trans_le (le_of_eq hM.symm)

section Embed

variable {G : Type*} [Group G]

structure Data (p : ℕ) (x y : G) : Prop where
  hx : x ^ p = 1
  hy : y ^ p = 1
  hz : ⁅x, y⁆ ^ p = 1
  hzx : ⁅x, y⁆ * x = x * ⁅x, y⁆
  hzy : ⁅x, y⁆ * y = y * ⁅x, y⁆
  hne : ⁅x, y⁆ ≠ 1

lemma pow_val_add [NeZero p] {g : G} (hg : g ^ p = 1) (k l : ZMod p) :
    g ^ (k + l).val = g ^ k.val * g ^ l.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod (k.val + l.val) hg, pow_add]

lemma pow_val_neg [NeZero p] {g : G} (hg : g ^ p = 1) (k : ZMod p) :
    g ^ (-k).val = (g ^ k.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_val_add hg, neg_add_cancel, ZMod.val_zero, pow_zero]

lemma pow_val_natCast [NeZero p] {g : G} (hg : g ^ p = 1) (n : ℕ) :
    g ^ n = g ^ (n : ZMod p).val := by
  rw [ZMod.val_natCast, pow_eq_pow_mod n hg]

lemma comm_pow_aux {x y z : G} (hzx : z * x = x * z) (hzy : z * y = y * z)
    (hxy : x * y = y * x * z) (n N : ℕ) :
    x ^ N * y ^ n = y ^ n * x ^ N * z ^ (N * n) := by
  have zy_pow : ∀ m : ℕ, z * y ^ m = y ^ m * z := fun m =>
    (Commute.pow_right (show Commute z y from hzy) m).eq
  have zx_pow : ∀ m : ℕ, z ^ m * x = x * z ^ m := fun m =>
    (Commute.pow_left (show Commute z x from hzx) m).eq
  have K1 : ∀ m : ℕ, x * y ^ m = y ^ m * x * z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc x * y ^ (m + 1) = (x * y) * y ^ m := by rw [pow_succ', mul_assoc]
        _ = (y * x * z) * y ^ m := by rw [hxy]
        _ = y * x * (z * y ^ m) := by simp only [mul_assoc]
        _ = y * x * (y ^ m * z) := by rw [zy_pow m]
        _ = y * (x * y ^ m) * z := by simp only [mul_assoc]
        _ = y * (y ^ m * x * z ^ m) * z := by rw [ih]
        _ = y ^ (m + 1) * x * z ^ (m + 1) := by
          rw [pow_succ' y m, pow_succ z m]; simp only [mul_assoc]
  induction N with
  | zero => simp
  | succ N ih =>
    calc x ^ (N + 1) * y ^ n = x ^ N * (x * y ^ n) := by rw [pow_succ, mul_assoc]
      _ = x ^ N * (y ^ n * x * z ^ n) := by rw [K1 n]
      _ = (x ^ N * y ^ n) * x * z ^ n := by simp only [mul_assoc]
      _ = (y ^ n * x ^ N * z ^ (N * n)) * x * z ^ n := by rw [ih]
      _ = y ^ n * x ^ N * (z ^ (N * n) * x) * z ^ n := by simp only [mul_assoc]
      _ = y ^ n * x ^ N * (x * z ^ (N * n)) * z ^ n := by rw [zx_pow (N * n)]
      _ = y ^ n * (x ^ N * x) * (z ^ (N * n) * z ^ n) := by simp only [mul_assoc]
      _ = y ^ n * x ^ (N + 1) * z ^ ((N + 1) * n) := by
          rw [← pow_succ, ← pow_add, add_one_mul]

lemma xy_eq (x y z : G) (hz : z = ⁅x, y⁆) (hzx : z * x = x * z) (hzy : z * y = y * z) :
    x * y = y * x * z := by
  have h0 : x * y = z * y * x := by
    rw [hz, commutatorElement_def]; group
  calc x * y = z * y * x := h0
    _ = y * z * x := by rw [hzy]
    _ = y * (z * x) := by rw [mul_assoc]
    _ = y * (x * z) := by rw [hzx]
    _ = y * x * z := by rw [mul_assoc]

lemma final_aux (A B C N B' C' W : G)
    (hK : N * B = B * N * W) (hWB : Commute W B') (hWC : Commute W C)
    (hWC' : Commute W C') (hCN : Commute C N) (hCB : Commute C B') :
    A * N * (B * B') * (C * C' * W⁻¹) = A * B * C * (N * B' * C') := by
  have hWCC : W * (C * C') = C * C' * W := (hWC.mul_right hWC').eq
  have hR : A * B * C * (N * B' * C') = A * B * N * B' * C * C' := by
    calc A * B * C * (N * B' * C') = A * B * (C * N) * B' * C' := by simp only [mul_assoc]
      _ = A * B * (N * C) * B' * C' := by rw [hCN.eq]
      _ = A * B * N * (C * B') * C' := by simp only [mul_assoc]
      _ = A * B * N * (B' * C) * C' := by rw [hCB.eq]
      _ = A * B * N * B' * C * C' := by simp only [mul_assoc]
  rw [hR]
  calc A * N * (B * B') * (C * C' * W⁻¹)
      = A * (N * B) * B' * (C * C' * W⁻¹) := by simp only [mul_assoc]
    _ = A * (B * N * W) * B' * (C * C' * W⁻¹) := by rw [hK]
    _ = A * B * N * (W * B') * (C * C' * W⁻¹) := by simp only [mul_assoc]
    _ = A * B * N * (B' * W) * (C * C' * W⁻¹) := by rw [hWB.eq]
    _ = A * B * N * B' * (W * (C * C')) * W⁻¹ := by simp only [mul_assoc]
    _ = A * B * N * B' * (C * C' * W) * W⁻¹ := by rw [hWCC]
    _ = A * B * N * B' * C * C' := by group

lemma lift_mul_aux [NeZero p] {x y : G} (h : Data p x y) (u v : Heis p) :
    x ^ (u * v).a.val * y ^ (u * v).b.val * ⁅x, y⁆ ^ (u * v).c.val =
      (x ^ u.a.val * y ^ u.b.val * ⁅x, y⁆ ^ u.c.val) *
        (x ^ v.a.val * y ^ v.b.val * ⁅x, y⁆ ^ v.c.val) := by
  have hzc : Commute ⁅x, y⁆ x := h.hzx
  have hzc' : Commute ⁅x, y⁆ y := h.hzy
  have hxy : x * y = y * x * ⁅x, y⁆ := xy_eq x y ⁅x, y⁆ rfl h.hzx h.hzy
  have hK := comm_pow_aux (x := x) (y := y) (z := ⁅x, y⁆) h.hzx h.hzy hxy u.b.val v.a.val
  have hcast : ((v.a.val * u.b.val : ℕ) : ZMod p) = v.a * u.b := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hW : ⁅x, y⁆ ^ (v.a.val * u.b.val) = ⁅x, y⁆ ^ (v.a * u.b).val := by
    rw [pow_val_natCast h.hz (v.a.val * u.b.val), hcast]
  rw [hW] at hK
  have hWB : Commute (⁅x, y⁆ ^ (v.a * u.b).val) (y ^ v.b.val) := hzc'.pow_pow _ _
  have hWC : Commute (⁅x, y⁆ ^ (v.a * u.b).val) (⁅x, y⁆ ^ u.c.val) :=
    (Commute.refl ⁅x, y⁆).pow_pow _ _
  have hWC' : Commute (⁅x, y⁆ ^ (v.a * u.b).val) (⁅x, y⁆ ^ v.c.val) :=
    (Commute.refl ⁅x, y⁆).pow_pow _ _
  have hCN : Commute (⁅x, y⁆ ^ u.c.val) (x ^ v.a.val) := (hzc.pow_left _).pow_right _
  have hCB : Commute (⁅x, y⁆ ^ u.c.val) (y ^ v.b.val) := (hzc'.pow_left _).pow_right _
  rw [mul_a, mul_b, mul_c, pow_val_add h.hx, pow_val_add h.hy, sub_eq_add_neg,
    pow_val_add h.hz, pow_val_add h.hz, pow_val_neg h.hz]
  exact final_aux _ _ _ _ _ _ _ hK hWB hWC hWC' hCN hCB

@[expose] def lift [NeZero p] {x y : G} (h : Data p x y) : Heis p →* G where
  toFun u := x ^ u.a.val * y ^ u.b.val * ⁅x, y⁆ ^ u.c.val
  map_one' := by simp
  map_mul' := fun u v => lift_mul_aux h u v

theorem lift_X [NeZero p] {x y : G} (h : Data p x y) (hp1 : 1 < p) : lift h X = x := by
  haveI : Fact (1 < p) := ⟨hp1⟩
  have e : lift h X = x ^ X.a.val * y ^ X.b.val * ⁅x, y⁆ ^ X.c.val := rfl
  rw [e]
  simp [X, ZMod.val_one, ZMod.val_zero]

theorem lift_Y [NeZero p] {x y : G} (h : Data p x y) (hp1 : 1 < p) : lift h Y = y := by
  haveI : Fact (1 < p) := ⟨hp1⟩
  have e : lift h Y = x ^ Y.a.val * y ^ Y.b.val * ⁅x, y⁆ ^ Y.c.val := rfl
  rw [e]
  simp [Y, ZMod.val_one, ZMod.val_zero]

theorem lift_apply [NeZero p] {x y : G} (h : Data p x y) (u : Heis p) :
    lift h u = x ^ u.a.val * y ^ u.b.val * ⁅x, y⁆ ^ u.c.val := rfl

lemma lift_injective_aux [NeZero p] {x y : G} (h : Data p x y) (hord : orderOf ⁅x, y⁆ = p) :
    Function.Injective (lift h) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hlift : ∀ t : ZMod p, lift h ⟨0, 0, t⟩ = ⁅x, y⁆ ^ t.val := fun t => by
    simp [lift_apply, ZMod.val_zero]
  have key : ∀ t : ZMod p, lift h ⟨0, 0, t⟩ = 1 → t = 0 := by
    intro t ht
    rw [hlift] at ht
    have hdvd : p ∣ t.val := by
      have := orderOf_dvd_of_pow_eq_one ht
      rwa [hord] at this
    have h0 : t.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt t)
    exact (ZMod.val_eq_zero t).mp h0
  have hA : ⁅u, Y⁆ = (⟨0, 0, u.a⟩ : Heis p) := by
    rw [comm_eq]; simp [Y]
  have hA1 : lift h ⁅u, Y⁆ = 1 := by
    rw [map_commutatorElement, hu, commutatorElement_one_left]
  have hB1 : lift h ⁅(X : Heis p), u⁆ = 1 := by
    rw [map_commutatorElement, hu, commutatorElement_one_right]
  have ha : u.a = 0 := by
    rw [hA] at hA1
    exact key _ hA1
  have hb : u.b = 0 := by
    rw [comm_eq] at hB1
    have h2 := key _ hB1
    simpa [X] using h2
  have hu_eq : u = ⟨0, 0, u.c⟩ := by
    ext <;> simp [ha, hb]
  have hc : lift h ⟨0, 0, u.c⟩ = 1 := by
    rw [← hu_eq]; exact hu
  have hc0 : u.c = 0 := key _ hc
  ext <;> simp [ha, hb, hc0]

theorem lift_injective [Fact p.Prime] (hp : p ≠ 2) {x y : G} (h : Data p x y) :
    Function.Injective (lift h) :=
  lift_injective_aux h (orderOf_eq_prime h.hz h.hne)

end Embed

section Conj

variable {p : ℕ}

theorem dataHeis [Fact p.Prime] (hp : p ≠ 2) {u v : Heis p} (hdet : u.a * v.b - u.b * v.a ≠ 0) :
    Data p u v where
  hx := pow_prime hp u
  hy := pow_prime hp v
  hz := pow_prime hp _
  hzx := by
    rw [comm_eq]
    ext <;> simp only [mul_a, mul_b, mul_c] <;> ring
  hzy := by
    rw [comm_eq]
    ext <;> simp only [mul_a, mul_b, mul_c] <;> ring
  hne := by
    rw [comm_eq]
    intro h
    have := congrArg Heis.c h
    exact hdet this

theorem lift_heis_a [Fact p.Prime] (hp : p ≠ 2) {u v : Heis p} (hdet : u.a * v.b - u.b * v.a ≠ 0)
    (h : Heis p) : (lift (dataHeis hp hdet) h).a = h.a * u.a + h.b * v.a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [lift_apply]
  simp only [mul_a, pow_eq, comm_eq, ZMod.natCast_zmod_val]
  ring

theorem lift_heis_b [Fact p.Prime] (hp : p ≠ 2) {u v : Heis p} (hdet : u.a * v.b - u.b * v.a ≠ 0)
    (h : Heis p) : (lift (dataHeis hp hdet) h).b = h.a * u.b + h.b * v.b := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [lift_apply]
  simp only [mul_b, pow_eq, comm_eq, ZMod.natCast_zmod_val]
  ring

theorem conj_map_Mline [Fact p.Prime] (hp : p ≠ 2) {G : Type*} [Group G] {φ : Heis p →* G}
    (hφ : Function.Injective φ) (g : G) (u v : Heis p)
    (hu : g * φ X * g⁻¹ = φ u) (hv : g * φ Y * g⁻¹ = φ v)
    (hdet : u.a * v.b - u.b * v.a ≠ 0) (w : ZMod p × ZMod p) (hw : w ≠ 0) :
    ((Mline w).map φ).map (MulAut.conj g).toMonoidHom =
      (Mline (u.a * w.1 + v.a * w.2, u.b * w.1 + v.b * w.2)).map φ := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hp1 : 1 < p := hpp.one_lt
  set ψ := lift (dataHeis hp hdet) with hψ
  have hconj : ∀ h : Heis p, g * φ h * g⁻¹ = φ (ψ h) := by
    have heq : ((MulAut.conj g).toMonoidHom.comp φ) = φ.comp ψ := by
      have hcl : Set.EqOn ((MulAut.conj g).toMonoidHom.comp φ) (φ.comp ψ)
          (Subgroup.closure ({X, Y} : Set (Heis p)) : Set (Heis p)) := by
        apply MonoidHom.eqOn_closure
        intro t ht
        rcases ht with rfl | ht
        · simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply]
          rw [hu, hψ, lift_X _ hp1]
        · simp only [Set.mem_singleton_iff] at ht
          subst ht
          simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply]
          rw [hv, hψ, lift_Y _ hp1]
      ext t
      have := hcl (by rw [closure_XY]; exact Set.mem_univ t)
      exact this
    intro h
    have := congrArg (fun f => f h) heq
    simpa [MulAut.conj_apply] using this
  have hAw : (u.a * w.1 + v.a * w.2, u.b * w.1 + v.b * w.2) ≠ 0 := by
    intro h0
    have h1 : u.a * w.1 + v.a * w.2 = 0 := congrArg Prod.fst h0
    have h2 : u.b * w.1 + v.b * w.2 = 0 := congrArg Prod.snd h0
    apply hw
    have e1 : (u.a * v.b - u.b * v.a) * w.1 = 0 := by linear_combination v.b * h1 - v.a * h2
    have e2 : (u.a * v.b - u.b * v.a) * w.2 = 0 := by linear_combination u.a * h2 - u.b * h1
    exact Prod.ext ((mul_eq_zero.1 e1).resolve_left hdet) ((mul_eq_zero.1 e2).resolve_left hdet)
  haveI : Finite (Heis p) :=
    Finite.of_injective (fun h : Heis p => (h.a, h.b, h.c)) (by
      intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact Heis.ext hxy.1 hxy.2.1 hxy.2.2)
  haveI : Finite ↥((Mline (u.a * w.1 + v.a * w.2, u.b * w.1 + v.b * w.2)).map φ) :=
    Finite.of_equiv _ (Subgroup.equivMapOfInjective _ φ hφ).toEquiv
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨ψ h, ?_, ?_⟩
    · show (ψ h).a * (u.b * w.1 + v.b * w.2) = (ψ h).b * (u.a * w.1 + v.a * w.2)
      have hh' : h.a * w.2 = h.b * w.1 := hh
      rw [hψ, lift_heis_a hp hdet, lift_heis_b hp hdet]
      linear_combination (u.a * v.b - u.b * v.a) * hh'
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      exact (hconj h).symm
  · rw [Subgroup.card_map_of_injective hφ, Subgroup.card_map_of_injective
      (MulAut.conj g).injective, Subgroup.card_map_of_injective hφ,
      Mline_card hw, Mline_card hAw]

end Conj

section Assembly

@[expose] def ConjSub {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B

theorem mem_map_conj {G : Type*} [Group G] (A : Subgroup G) (g x : G) :
    x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem ConjSub.refl {G : Type*} [Group G] (A : Subgroup G) : ConjSub A A :=
  ⟨1, by
    ext x
    rw [mem_map_conj]
    simp⟩

theorem ConjSub.symm {G : Type*} [Group G] {A B : Subgroup G} (h : ConjSub A B) :
    ConjSub B A := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  ext x
  rw [mem_map_conj, mem_map_conj]
  simp [mul_assoc]

theorem ConjSub.trans {G : Type*} [Group G] {A B C : Subgroup G} (h₁ : ConjSub A B)
    (h₂ : ConjSub B C) : ConjSub A C := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  refine ⟨h * g, ?_⟩
  ext x
  rw [mem_map_conj, mem_map_conj, mem_map_conj]
  simp [mul_assoc]

variable {p : ℕ}

theorem exists_conj_mline [Fact p.Prime] (hp : p ≠ 2) {G : Type*} [Group G] [Finite G]
    {φ : Heis p →* G} (hφ : Function.Injective φ) (hsyl : ¬ p ^ 4 ∣ Nat.card G)
    (B : Subgroup G) (hB : Nat.card B = p ^ 2) :
    ∃ v : ZMod p × ZMod p, v ≠ 0 ∧ ConjSub B ((Mline v).map φ) := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : Finite (Heis p) := Finite.of_injective φ hφ
  have hP3 : Nat.card φ.range = p ^ 3 := by
    rw [← card_heis (p := p)]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have hPp : IsPGroup p φ.range := IsPGroup.of_card hP3
  have hidx : ¬ p ∣ φ.range.index := by
    intro hdvd
    apply hsyl
    have h := φ.range.index_mul_card
    rw [hP3] at h
    rw [← h]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk]
    exact ⟨k, by ring⟩
  let S : Sylow p G := hPp.toSylow hidx
  have hBp : IsPGroup p B := IsPGroup.of_card hB
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hQ : ∀ x : G, x ∈ (Q : Subgroup G) ↔ g⁻¹ * x * g ∈ φ.range := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    have := mem_map_conj φ.range g x
    simpa [S] using this
  have hB'P : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ φ.range := by
    intro x hx
    rw [mem_map_conj] at hx
    have hx' : g * x * g⁻¹ ∈ B := by simpa using hx
    have hxQ : g * x * g⁻¹ ∈ (Q : Subgroup G) := hBQ hx'
    have := (hQ _).1 hxQ
    simpa [mul_assoc] using this
  set M : Subgroup (Heis p) := (B.map (MulAut.conj g⁻¹).toMonoidHom).comap φ with hM
  have hMmap : M.map φ = B.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_comap_eq_self hB'P
  have hMcard : Nat.card M = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hφ, hMmap,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hB]
  obtain ⟨v, hv0, hMv⟩ := exists_Mline hp M hMcard
  refine ⟨v, hv0, ⟨g⁻¹, ?_⟩⟩
  rw [← hMmap, hMv]

theorem oneClassE [Fact p.Prime] (hp : p ≠ 2) {G : Type*} [Group G] [Finite G] {x y : G}
    (hd : Data p x y) (hsyl : ¬ p ^ 4 ∣ Nat.card G)
    (As : Set (Matrix (Fin 2) (Fin 2) (ZMod p)))
    (hconj : ∀ A ∈ As, ∃ g : G, ∃ a b c a' b' c' : ℕ,
      A = !![(a : ZMod p), (a' : ZMod p); (b : ZMod p), (b' : ZMod p)] ∧
        g * x * g⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ c ∧ g * y * g⁻¹ = x ^ a' * y ^ b' * ⁅x, y⁆ ^ c')
    (htrans : ∀ w : Fin 2 → ZMod p, w ≠ 0 →
      ∃ A ∈ Submonoid.closure As, ∃ s : ZMod p, s ≠ 0 ∧ A.mulVec ![1, 0] = s • w) :
    ∀ B U : Subgroup G, Nat.card B = p ^ 2 → Nat.card U = p ^ 2 → ConjSub B U := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hp1 : 1 < p := hpp.one_lt
  set φ := lift hd with hφdef
  have hφ : Function.Injective φ := lift_injective hp hd
  have hclaim : ∀ A ∈ Submonoid.closure As, A.det ≠ 0 ∧ ∃ h : G, ∀ w : Fin 2 → ZMod p, w ≠ 0 →
      ((Mline (w 0, w 1)).map φ).map (MulAut.conj h).toMonoidHom =
        (Mline ((A.mulVec w) 0, (A.mulVec w) 1)).map φ := by
    intro A hA
    induction hA using Submonoid.closure_induction with
    | mem A hA =>
      obtain ⟨g, a, b, c, a', b', c', rfl, hgx, hgy⟩ := hconj A hA
      set u : Heis p := ⟨(a : ZMod p), (b : ZMod p), (c : ZMod p)⟩ with hu
      set v : Heis p := ⟨(a' : ZMod p), (b' : ZMod p), (c' : ZMod p)⟩ with hv
      have hxu : g * φ X * g⁻¹ = φ u := by
        rw [hφdef, lift_X hd hp1, hgx, lift_apply]
        simp only [hu, ZMod.val_natCast]
        rw [← pow_eq_pow_mod _ hd.hx, ← pow_eq_pow_mod _ hd.hy, ← pow_eq_pow_mod _ hd.hz]
      have hyv : g * φ Y * g⁻¹ = φ v := by
        rw [hφdef, lift_Y hd hp1, hgy, lift_apply]
        simp only [hv, ZMod.val_natCast]
        rw [← pow_eq_pow_mod _ hd.hx, ← pow_eq_pow_mod _ hd.hy, ← pow_eq_pow_mod _ hd.hz]
      have hdet : u.a * v.b - u.b * v.a ≠ 0 := by
        intro h0
        have hcomm : ⁅u, v⁆ = 1 := by
          rw [comm_eq]
          ext <;> simp [h0]
        have h1 : g * ⁅x, y⁆ * g⁻¹ = 1 := by
          have := map_commutatorElement (MulAut.conj g).toMonoidHom x y
          have e1 : (MulAut.conj g).toMonoidHom x = φ u := by
            simpa [MulAut.conj_apply, hφdef, lift_X hd hp1] using hxu
          have e2 : (MulAut.conj g).toMonoidHom y = φ v := by
            simpa [MulAut.conj_apply, hφdef, lift_Y hd hp1] using hyv
          rw [e1, e2, ← map_commutatorElement, hcomm, map_one] at this
          simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] using this
        apply hd.hne
        calc ⁅x, y⁆ = g⁻¹ * (g * ⁅x, y⁆ * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      refine ⟨?_, g, fun w hw => ?_⟩
      · rw [Matrix.det_fin_two_of]
        intro h0
        apply hdet
        simp only [hu, hv]
        linear_combination h0
      · have := conj_map_Mline hp hφ g u v hxu hyv hdet (w 0, w 1) (by
          intro h0
          apply hw
          ext i
          fin_cases i
          · exact congrArg Prod.fst h0
          · exact congrArg Prod.snd h0)
        convert this using 3 <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu, hv]
    | one =>
      refine ⟨by simp, 1, fun w hw => ?_⟩
      have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext t; simp
      rw [this, Subgroup.map_id, Matrix.one_mulVec]
    | mul A B _ _ ihA ihB =>
      obtain ⟨hdA, h1, hh1⟩ := ihA
      obtain ⟨hdB, h2, hh2⟩ := ihB
      refine ⟨by rw [Matrix.det_mul]; exact mul_ne_zero hdA hdB, h1 * h2, fun w hw => ?_⟩
      have hBw : B.mulVec w ≠ 0 := fun h0 => hw (Matrix.eq_zero_of_mulVec_eq_zero hdB h0)
      have e1 := hh2 w hw
      have e2 := hh1 (B.mulVec w) hBw
      rw [Matrix.mulVec_mulVec] at e2
      have hc : (MulAut.conj (h1 * h2)).toMonoidHom =
          (MulAut.conj h1).toMonoidHom.comp (MulAut.conj h2).toMonoidHom := by
        ext t
        simp [mul_assoc]
      rw [hc, ← Subgroup.map_map, e1, e2]
  have hmove : ∀ v : ZMod p × ZMod p, v ≠ 0 →
      ConjSub ((Mline (1, 0)).map φ) ((Mline v).map φ) := by
    intro v hv
    obtain ⟨A, hA, s, hs, hAv⟩ := htrans ![v.1, v.2] (by
      intro h0
      apply hv
      ext
      · simpa using congrFun h0 0
      · simpa using congrFun h0 1)
    obtain ⟨-, h, hh⟩ := hclaim A hA
    refine ⟨h, ?_⟩
    have := hh ![1, 0] (by
      intro h0
      have := congrFun h0 0
      simp at this)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this, hAv]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Mline_smul hs]
  intro B U hB hU
  obtain ⟨v, hv, hBv⟩ := exists_conj_mline hp hφ hsyl B hB
  obtain ⟨w, hw, hUw⟩ := exists_conj_mline hp hφ hsyl U hU
  exact hBv.trans ((hmove v hv).symm.trans ((hmove w hw).trans hUw.symm))

end Assembly

section Reach

variable {p : ℕ}

@[expose] def reach (As : List (Matrix (Fin 2) (Fin 2) (ZMod p))) : ℕ → List (Fin 2 → ZMod p)
  | 0 => [![1, 0]]
  | n + 1 => reach As n ++ (reach As n).flatMap fun v => As.map fun A => A.mulVec v

theorem reach_sound (As : List (Matrix (Fin 2) (Fin 2) (ZMod p))) (n : ℕ) :
    ∀ v ∈ reach As n, ∃ A ∈ Submonoid.closure {A | A ∈ As}, A.mulVec ![1, 0] = v := by
  induction n with
  | zero =>
    intro v hv
    simp only [reach, List.mem_singleton] at hv
    exact ⟨1, Submonoid.one_mem _, by rw [hv, Matrix.one_mulVec]⟩
  | succ n ih =>
    intro v hv
    simp only [reach, List.mem_append, List.mem_flatMap, List.mem_map] at hv
    rcases hv with hv | ⟨u, hu, B, hB, rfl⟩
    · exact ih v hv
    · obtain ⟨A, hA, hAu⟩ := ih u hu
      refine ⟨B * A, Submonoid.mul_mem _ (Submonoid.subset_closure hB) hA, ?_⟩
      rw [← Matrix.mulVec_mulVec, hAu]

theorem trans_of_reach (As : List (Matrix (Fin 2) (Fin 2) (ZMod p))) (n : ℕ)
    (h : ∀ w : Fin 2 → ZMod p, w ≠ 0 → ∃ s : ZMod p, s ≠ 0 ∧ s • w ∈ reach As n) :
    ∀ w : Fin 2 → ZMod p, w ≠ 0 →
      ∃ A ∈ Submonoid.closure {A | A ∈ As}, ∃ s : ZMod p, s ≠ 0 ∧ A.mulVec ![1, 0] = s • w := by
  intro w hw
  obtain ⟨s, hs, hsw⟩ := h w hw
  obtain ⟨A, hA, hAw⟩ := reach_sound As n _ hsw
  exact ⟨A, hA, s, hs, hAw⟩

end Reach

end Heis

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
