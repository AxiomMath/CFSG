module

public import Certificates.Data.Kernel.D5TwistF
public import CFSG.Certificates.Kernel.D5TwistKSound
import Mathlib.Tactic.IntervalCases

public section

namespace Certificates.D5TwistK

open Certificates.D5Twist

@[expose] def bv (b1 b2 : Bool) : Nat := (if b1 then 1 else 0) + (if b2 then 2 else 0)

@[expose] def mulB (a1 a2 b1 b2 : Bool) : Bool × Bool :=
  (a1 && b1 || a2 && b2, a1 && b2 || a2 && b1)

@[expose] def addB (u v : Bool × Bool) : Bool × Bool :=
  ((u.2 || v.2) ^^ ((u.1 || v.2) ^^ (u.2 || v.1)), (u.1 || v.1) ^^ ((u.1 || v.2) ^^ (u.2 || v.1)))

theorem bv_mulB : ∀ a1 a2 b1 b2 : Bool, (a1 && a2) = false → (b1 && b2) = false →
    bv (mulB a1 a2 b1 b2).1 (mulB a1 a2 b1 b2).2 = bv a1 a2 * bv b1 b2 % 3 ∧
      ((mulB a1 a2 b1 b2).1 && (mulB a1 a2 b1 b2).2) = false := by decide

theorem bv_addB4 : ∀ u1 u2 v1 v2 : Bool, (u1 && u2) = false → (v1 && v2) = false →
    bv (addB (u1, u2) (v1, v2)).1 (addB (u1, u2) (v1, v2)).2 = (bv u1 u2 + bv v1 v2) % 3 ∧
      ((addB (u1, u2) (v1, v2)).1 && (addB (u1, u2) (v1, v2)).2) = false := by decide

theorem bv_addB (u v : Bool × Bool) (hu : (u.1 && u.2) = false) (hv : (v.1 && v.2) = false) :
    bv (addB u v).1 (addB u v).2 = (bv u.1 u.2 + bv v.1 v.2) % 3 ∧
      ((addB u v).1 && (addB u v).2) = false := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  exact bv_addB4 u1 u2 v1 v2 hu hv

theorem bv_nrm : ∀ a b : Bool, bv (a && !b) (b && !a) = bv a b % 3 ∧
    ((a && !b) && (b && !a)) = false := by decide

theorem addB_ff : addB (false, false) (false, false) = (false, false) := rfl

theorem dg_bits (Z p : Nat) : dg Z p = bv (Z.testBit (2 * p)) (Z.testBit (2 * p + 1)) := by
  have e : Z / 4 ^ p = Z >>> (2 * p) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  have h0 : Z.testBit (2 * p) = (Z >>> (2 * p)).testBit 0 := by
    rw [Nat.testBit_shiftRight, Nat.add_zero]
  have h1 : Z.testBit (2 * p + 1) = (Z >>> (2 * p)).testBit 1 := by rw [Nat.testBit_shiftRight]
  rw [dg_eq, e, h0, h1]
  generalize Z >>> (2 * p) = w
  rw [Nat.testBit_succ, Nat.testBit_zero, Nat.testBit_zero]
  unfold bv
  by_cases a : w % 2 = 1 <;> by_cases b : w / 2 % 2 = 1 <;> simp [a, b] <;> omega

theorem tb_big {c n : Nat} (hc : c < 2 ^ n) {q : Nat} (hq : n ≤ q) : c.testBit q = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hq))

theorem tb_LF (q : Nat) : LF.testBit q = decide (q < 50 ∧ q % 2 = 0) := by
  by_cases hq : q < 50
  · revert q
    decide
  · rw [tb_big (n := 50) (by decide) (by omega)]
    simp [hq]

theorem tb_CMF (q : Nat) : CMF.testBit q = decide (q < 50 ∧ q % 10 < 2) := by
  by_cases hq : q < 50
  · revert q
    decide
  · rw [tb_big (n := 50) (by decide) (by omega)]
    simp [hq]

theorem tb_1023 (q : Nat) : (1023 : Nat).testBit q = decide (q < 10) := by
  by_cases hq : q < 10
  · revert q
    decide
  · rw [tb_big (n := 10) (by decide) (by omega)]
    simp [hq]

theorem land_e (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem lor_e (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem xor_e (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem shr_e (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem shl_e (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl

theorem tb_colF (x j q : Nat) (hj : j < 5) (hq : q < 50) :
    (colF x j).testBit q = x.testBit (10 * (q / 10) + 2 * j + q % 2) := by
  simp only [colF, land_e, lor_e, shl_e, shr_e, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, tb_CMF]
  interval_cases q <;> simp <;> (congr 1; omega)

theorem tb_rowF (y j q : Nat) (hj : j < 5) (hq : q < 50) :
    (rowF y j).testBit q = y.testBit (10 * j + q % 10) := by
  simp only [rowF, land_e, lor_e, shl_e, shr_e, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, tb_1023]
  interval_cases q <;> simp <;> (congr 1; omega)

theorem tb_nrmF (x p : Nat) (hp : p < 25) :
    (nrmF x).testBit (2 * p) = (x.testBit (2 * p) && !x.testBit (2 * p + 1)) ∧
      (nrmF x).testBit (2 * p + 1) = (x.testBit (2 * p + 1) && !x.testBit (2 * p)) := by
  simp only [nrmF, land_e, lor_e, xor_e, shl_e, shr_e, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, tb_LF]
  have xa1 : ∀ a b : Bool, (a ^^ (a && b)) = (a && !b) := by decide
  have xa2 : ∀ a b : Bool, (b ^^ (a && b)) = (b && !a) := by decide
  interval_cases p <;> simp [xa1, xa2] <;> grind

@[expose] def pl (z : Nat × Nat) (q : Nat) : Bool × Bool := (z.1.testBit q, z.2.testBit q)

theorem pl_addF (a b : Nat × Nat) (q : Nat) : pl (addF a b) q = addB (pl a q) (pl b q) := by
  simp only [pl, addF, addB, lor_e, xor_e, Nat.testBit_or, Nat.testBit_xor]

theorem pl_termF (X Y q : Nat) : pl (termF X Y) q =
    if LF.testBit q then mulB (X.testBit q) (X.testBit (q + 1)) (Y.testBit q) (Y.testBit (q + 1))
    else (false, false) := by
  simp only [pl, termF, mulB, land_e, lor_e, shr_e, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftRight]
  cases LF.testBit q <;> simp [Nat.add_comm 1 q]

theorem pl_tjF_odd (x y j q : Nat) (hq : q % 2 = 1) : pl (tjF x y j) q = (false, false) := by
  rw [tjF, pl_termF, tb_LF]
  simp [hq]

theorem pl_tjF_big (x y j q : Nat) (hq : 50 ≤ q) : pl (tjF x y j) q = (false, false) := by
  rw [tjF, pl_termF, tb_LF, if_neg (by simp; omega)]

theorem pl_tjF (x y i j k : Nat) (hi : i < 5) (hj : j < 5) (hk : k < 5) :
    pl (tjF x y j) (2 * (5 * i + k)) =
      mulB (x.testBit (2 * (5 * i + j))) (x.testBit (2 * (5 * i + j) + 1))
        (y.testBit (2 * (5 * j + k))) (y.testBit (2 * (5 * j + k) + 1)) := by
  have hq0 : 2 * (5 * i + k) < 50 := by omega
  have hq1 : 2 * (5 * i + k) + 1 < 50 := by omega
  rw [tjF, pl_termF, tb_LF, if_pos (by simp; omega), tb_colF _ _ _ hj hq0,
    tb_colF _ _ _ hj hq1, tb_rowF _ _ _ hj hq0, tb_rowF _ _ _ hj hq1]
  have e1 : 10 * (2 * (5 * i + k) / 10) + 2 * j + 2 * (5 * i + k) % 2 = 2 * (5 * i + j) := by
    omega
  have e2 : 10 * ((2 * (5 * i + k) + 1) / 10) + 2 * j + (2 * (5 * i + k) + 1) % 2 =
      2 * (5 * i + j) + 1 := by omega
  have e3 : 10 * j + 2 * (5 * i + k) % 10 = 2 * (5 * j + k) := by omega
  have e4 : 10 * j + (2 * (5 * i + k) + 1) % 10 = 2 * (5 * j + k) + 1 := by omega
  rw [e1, e2, e3, e4]

@[expose] noncomputable def sumF (x y : Nat) : Nat × Nat :=
  addF (addF (addF (addF (tjF x y 0) (tjF x y 1)) (tjF x y 2)) (tjF x y 3)) (tjF x y 4)

theorem mulNF_eq (x y : Nat) : mulNF x y = (sumF x y).1 ||| ((sumF x y).2 <<< 1) := rfl

theorem pl_sumF_odd (x y q : Nat) (hq : q % 2 = 1) : pl (sumF x y) q = (false, false) := by
  simp only [sumF, pl_addF, pl_tjF_odd _ _ _ _ hq, addB_ff]

theorem pl_sumF_big (x y q : Nat) (hq : 50 ≤ q) : pl (sumF x y) q = (false, false) := by
  simp only [sumF, pl_addF, pl_tjF_big _ _ _ _ hq, addB_ff]

theorem tb_sumF2_big (x y r : Nat) (hr : 49 ≤ r) : (sumF x y).2.testBit r = false := by
  by_cases ho : r % 2 = 1
  · have h := pl_sumF_odd x y r ho
    simp only [pl, Prod.mk.injEq] at h
    exact h.2
  · have h := pl_sumF_big x y r (by omega)
    simp only [pl, Prod.mk.injEq] at h
    exact h.2

theorem tb_mulNF_big (x y q : Nat) (hq : 50 ≤ q) : (mulNF x y).testBit q = false := by
  have h1 := pl_sumF_big x y q hq
  simp only [pl, Prod.mk.injEq] at h1
  rw [mulNF_eq, Nat.testBit_or, Nat.testBit_shiftLeft, h1.1, tb_sumF2_big x y (q - 1) (by omega)]
  simp

theorem mulNF_lt (x y : Nat) : mulNF x y < 4 ^ 25 := by
  have : (4 : Nat) ^ 25 = 2 ^ 50 := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  rw [this]
  exact Nat.lt_pow_two_of_testBit _ fun q hq => tb_mulNF_big x y q hq

theorem dg_mulNF (x y p : Nat) (hp : p < 25) :
    dg (mulNF x y) p = bv (pl (sumF x y) (2 * p)).1 (pl (sumF x y) (2 * p)).2 := by
  have h2 := pl_sumF_odd x y (2 * p + 1) (by omega)
  simp only [pl, Prod.mk.injEq] at h2
  have hc : (decide (2 * p ≥ 1) && (sumF x y).2.testBit (2 * p - 1)) = false := by
    by_cases hp0 : p = 0
    · subst hp0
      rfl
    · have h1 := pl_sumF_odd x y (2 * p - 1) (by omega)
      simp only [pl, Prod.mk.injEq] at h1
      rw [h1.2, Bool.and_false]
  have e : 2 * p + 1 - 1 = 2 * p := by omega
  rw [dg_bits, mulNF_eq, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_or,
    Nat.testBit_shiftLeft, h2.1, hc, e, Bool.or_false]
  simp [pl]

theorem nrm_pair (x m : Nat) (hm : m < 25) :
    bv ((nrmF x).testBit (2 * m)) ((nrmF x).testBit (2 * m + 1)) = dg x m % 3 ∧
      ((nrmF x).testBit (2 * m) && (nrmF x).testBit (2 * m + 1)) = false := by
  rw [(tb_nrmF x m hm).1, (tb_nrmF x m hm).2, dg_bits]
  exact bv_nrm _ _

theorem dg_mulF (x y p : Nat) (hp : p < 25) : dg (mulF x y) p = entK x y p := by
  obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < 5 ∧ k < 5 ∧ p = 5 * i + k :=
    ⟨p / 5, p % 5, by omega, by omega, by omega⟩
  rw [mulF, dg_mulNF _ _ _ hp]
  have hT : ∀ j, j < 5 → pl (tjF (nrmF x) (nrmF y) j) (2 * (5 * i + k)) =
      mulB ((nrmF x).testBit (2 * (5 * i + j))) ((nrmF x).testBit (2 * (5 * i + j) + 1))
        ((nrmF y).testBit (2 * (5 * j + k))) ((nrmF y).testBit (2 * (5 * j + k) + 1)) :=
    fun j hj => pl_tjF _ _ i j k hi hj hk
  have hM : ∀ j, j < 5 → bv (pl (tjF (nrmF x) (nrmF y) j) (2 * (5 * i + k))).1
      (pl (tjF (nrmF x) (nrmF y) j) (2 * (5 * i + k))).2 =
        dg x (5 * i + j) % 3 * (dg y (5 * j + k) % 3) % 3 ∧
      ((pl (tjF (nrmF x) (nrmF y) j) (2 * (5 * i + k))).1 &&
        (pl (tjF (nrmF x) (nrmF y) j) (2 * (5 * i + k))).2) = false := by
    intro j hj
    rw [hT j hj]
    obtain ⟨ex, hx⟩ := nrm_pair x (5 * i + j) (by omega)
    obtain ⟨ey, hy⟩ := nrm_pair y (5 * j + k) (by omega)
    obtain ⟨e, h⟩ := bv_mulB _ _ _ _ hx hy
    rw [e, ex, ey]
    exact ⟨rfl, h⟩
  have hA : ∀ u v : Bool × Bool, (u.1 && u.2) = false → (v.1 && v.2) = false →
      bv (addB u v).1 (addB u v).2 = (bv u.1 u.2 + bv v.1 v.2) % 3 ∧
        ((addB u v).1 && (addB u v).2) = false := bv_addB
  obtain ⟨m0, o0⟩ := hM 0 (by decide)
  obtain ⟨m1, o1⟩ := hM 1 (by decide)
  obtain ⟨m2, o2⟩ := hM 2 (by decide)
  obtain ⟨m3, o3⟩ := hM 3 (by decide)
  obtain ⟨m4, o4⟩ := hM 4 (by decide)
  obtain ⟨s1, p1⟩ := hA _ _ o0 o1
  obtain ⟨s2, p2⟩ := hA _ _ p1 o2
  obtain ⟨s3, p3⟩ := hA _ _ p2 o3
  obtain ⟨s4, _⟩ := hA _ _ p3 o4
  simp only [sumF, pl_addF]
  rw [s4, s3, s2, s1, m0, m1, m2, m3, m4]
  have ei : (5 * i + k) / 5 = i := by omega
  have ek : (5 * i + k) % 5 = k := by omega
  unfold entK
  rw [ei, ek]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.zero_add]
  rw [← Nat.mul_mod, ← Nat.mul_mod, ← Nat.mul_mod, ← Nat.mul_mod, ← Nat.mul_mod]
  have e1 : 5 * 1 + k = 5 + k := by omega
  have e2 : 5 * 2 + k = 10 + k := by omega
  have e3 : 5 * 3 + k = 15 + k := by omega
  have e4 : 5 * 4 + k = 20 + k := by omega
  rw [e1, e2, e3, e4]
  omega

theorem mulF_eq : mulF = mulK := by
  funext x y
  have hl : mulF x y / 4 ^ 0 < 4 ^ 25 := by
    rw [Nat.pow_zero, Nat.div_one]
    exact mulNF_lt _ _
  have e := pk_dg 25 0 (mulF x y) hl
  rw [Nat.pow_zero, Nat.div_one] at e
  rw [← e, mulK]
  exact pk_congr _ _ 25 0 fun i _ hi => dg_mulF x y i (by omega)

theorem ccaF_eq (gens : List Nat) : ∀ n front seen, ccaF gens n front seen = ccaK gens n front seen := by
  intro n
  induction n with
  | zero => intro front seen; rfl
  | succ n ih =>
    intro front seen
    cases front with
    | nil => rfl
    | cons r front =>
      simp only [ccaF, ccaK, mulF_eq, ih]

theorem invAuxF_eq (g : Nat) : ∀ n cur prev, invAuxF g n cur prev = invAuxK g n cur prev := by
  intro n
  induction n with
  | zero => intro cur prev; rfl
  | succ n ih =>
    intro cur prev
    simp only [invAuxF, invAuxK, mulF_eq, ih]

theorem ccF_eq : ccF = ccK := by
  funext seed gens
  exact ccaF_eq gens 500 seed seed

theorem S0F_eq : S0F () = S0K () := by rw [S0F, S0K, ccF_eq]

theorem spF_eq : spF = spK := by
  funext ra
  rw [spF, spK, ccF_eq]

theorem wjF_eq : wjF = wjK := by
  funext b
  rw [wjF, wjK, ccF_eq]

theorem linesF_eq : linesF = linesK := by
  funext b
  rw [linesF, linesK, wjF_eq]

theorem rzF_eq : rzF = rzK := by
  funext ra z
  rw [rzF, rzK, spF_eq]

theorem ozF_eq : ozF = ozK := by
  funext b ra z
  rw [ozF, ozK, ccF_eq, wjF_eq, rzF_eq]

theorem lines15F_eq : lines15F = lines15K := by
  funext b ra
  rw [lines15F, lines15K, linesF_eq, ozF_eq]

theorem forcedF_eq : forcedF = forcedK := by
  funext b ra
  rw [forcedF, forcedK, lines15F_eq, ozF_eq]

theorem clF_eq : clF = clK := by
  funext b ra
  rw [clF, clK, ccF_eq, S0F_eq, forcedF_eq]

theorem restF_eq : restF = restK := by
  funext gs sp wj lines lines15 oz forced cl
  rw [restF, restK, mulF_eq]

theorem BF_eq (b ra : Nat) : BF b ra = BK b ra := by
  rw [BF, BK, restF_eq, spF_eq, wjF_eq, linesF_eq, lines15F_eq, ozF_eq, forcedF_eq, clF_eq]

theorem ch712503BF_eq (i : Nat) : ch712503BF i = ch712503B i := by
  rw [ch712503BF, ch712503B, BF_eq]

theorem ch712503SF_eq : ch712503SF () = ch712503S () := by
  rw [ch712503SF, ch712503S, S0F_eq, mulF_eq]

theorem caseAF_eq (b : Nat) (gA : Array Nat) (neg : Bool) (w : List Nat) :
    caseAF b gA neg w = caseAK b gA neg w := by
  simp only [caseAF, caseAK, caseAF2, caseAK2, caseAF3, caseAK3, invF, invK, invAuxF_eq,
    prodWordF, prodWordK, raF, raK, negF, negK, mulF_eq]

theorem ch712503AF_eq : ch712503AF () = ch712503A () := by
  simp only [ch712503AF, ch712503A, caseAF_eq]

end Certificates.D5TwistK

end
