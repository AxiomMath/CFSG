module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev GL12 : Type := GL (Fin 12) (ZMod 2)

abbrev Mat12 : Type := Matrix (Fin 12) (Fin 12) (ZMod 2)

@[expose] def rowsOf (k : ℕ) : Array ℕ :=
  Array.ofFn (n := 12) fun i => (k >>> (12 * (i : ℕ))) % 4096

@[expose] def keyAux (R : Array ℕ) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i => acc ||| ((R.getD i 0 % 4096) <<< (12 * i))) 0

@[expose] def keyOf (R : Array ℕ) : ℕ := keyAux R 12

@[expose] def toMatK (k : ℕ) : Mat12 := Matrix.of fun i j => bz (k.testBit (12 * (i : ℕ) + j))

@[expose] def mulK (a b : ℕ) : ℕ := keyOf (bmul 12 12 (rowsOf a) (rowsOf b))

@[expose] def idRows : Array ℕ := Array.ofFn (n := 12) fun i => 2 ^ (i : ℕ)

@[expose] def idK : ℕ := keyOf idRows

@[expose] def powK (a : ℕ) : ℕ → ℕ
  | 0 => idK
  | n + 1 => mulK (powK a n) a

theorem testBit_keyAux (R : Array ℕ) (n p : ℕ) :
    (keyAux R n).testBit p = (decide (p < 12 * n) && (R.getD (p / 12) 0).testBit (p % 12)) := by
  induction n with
  | zero => simp [keyAux]
  | succ n ih =>
    have e : keyAux R (n + 1) = keyAux R n ||| ((R.getD n 0 % 4096) <<< (12 * n)) := by
      rw [keyAux, List.range_succ, List.foldl_append]
      rfl
    rw [e, Nat.testBit_or, ih, Nat.testBit_shiftLeft, show (4096 : ℕ) = 2 ^ 12 by norm_num,
      Nat.testBit_mod_two_pow]
    by_cases h1 : p < 12 * n
    · have h2 : ¬ p ≥ 12 * n := by omega
      simp [h1, h2, show p < 12 * (n + 1) by omega]
    · by_cases h3 : p < 12 * (n + 1)
      · have hq : p / 12 = n := by omega
        have hr : p % 12 = p - 12 * n := by omega
        simp [h1, h3, hq, hr, show p ≥ 12 * n by omega, show p - 12 * n < 12 by omega]
      · simp [h1, h3, show ¬ p - 12 * n < 12 by omega]

theorem testBit_keyOf (R : Array ℕ) (p : ℕ) :
    (keyOf R).testBit p = (decide (p < 144) && (R.getD (p / 12) 0).testBit (p % 12)) :=
  testBit_keyAux R 12 p

theorem keyAux_lt (R : Array ℕ) (n : ℕ) (hn : n ≤ 12) : keyAux R n < 2 ^ 144 := by
  induction n with
  | zero => simp [keyAux]
  | succ n ih =>
    have e : keyAux R (n + 1) = keyAux R n ||| ((R.getD n 0 % 4096) <<< (12 * n)) := by
      rw [keyAux, List.range_succ, List.foldl_append]
      rfl
    rw [e]
    refine Nat.or_lt_two_pow (ih (by omega)) ?_
    rw [Nat.shiftLeft_eq]
    have h1 : R.getD n 0 % 4096 < 2 ^ 12 := Nat.mod_lt _ (by norm_num)
    calc R.getD n 0 % 4096 * 2 ^ (12 * n) < 2 ^ 12 * 2 ^ (12 * n) :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (12 * n + 12) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ 144 := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem keyOf_lt (R : Array ℕ) : keyOf R < 2 ^ 144 := keyAux_lt R 12 le_rfl

theorem mulK_lt (a b : ℕ) : mulK a b < 2 ^ 144 := keyOf_lt _

theorem idK_lt : idK < 2 ^ 144 := keyOf_lt _

theorem powK_lt (a n : ℕ) : powK a n < 2 ^ 144 := by
  cases n with
  | zero => exact idK_lt
  | succ n => exact mulK_lt _ _

theorem toMatK_keyOf (R : Array ℕ) : toMatK (keyOf R) = toMat 12 12 R := by
  ext i j
  rw [toMatK, Matrix.of_apply, toMat_apply, testBit_keyOf]
  have h1 : 12 * (i : ℕ) + j < 144 := by omega
  have h2 : (12 * (i : ℕ) + j) / 12 = i := by omega
  have h3 : (12 * (i : ℕ) + j) % 12 = j := by omega
  simp [h1, h2, h3]

theorem toMat_rowsOf (k : ℕ) : toMat 12 12 (rowsOf k) = toMatK k := by
  ext i j
  rw [toMat_apply, rowsOf, getD_ofFn, toMatK, Matrix.of_apply,
    show (4096 : ℕ) = 2 ^ 12 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp

theorem toMatK_mulK (a b : ℕ) : toMatK (mulK a b) = toMatK a * toMatK b := by
  rw [mulK, toMatK_keyOf, toMat_bmul, toMat_rowsOf, toMat_rowsOf]

theorem toMatK_idK : toMatK idK = 1 := by
  rw [idK, toMatK_keyOf]
  exact toMat_eq_one_of_bIsId (by decide)

theorem toMatK_powK (a n : ℕ) : toMatK (powK a n) = toMatK a ^ n := by
  induction n with
  | zero => rw [powK, toMatK_idK, pow_zero]
  | succ n ih => rw [powK, toMatK_mulK, ih, pow_succ]

theorem bz_injective : Function.Injective bz := by
  intro x y h
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem eq_of_toMatK_eq {a b : ℕ} (ha : a < 2 ^ 144) (hb : b < 2 ^ 144)
    (h : toMatK a = toMatK b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 144
  · have e := congrFun (congrFun h ⟨p / 12, by omega⟩) ⟨p % 12, Nat.mod_lt _ (by norm_num)⟩
    simp only [toMatK, Matrix.of_apply] at e
    have hp' : 12 * (p / 12) + p % 12 = p := Nat.div_add_mod p 12
    rw [hp'] at e
    exact bz_injective e
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]


@[expose] def glOf (a a' : ℕ) : GL12 :=
  if h : mulK a a' = idK ∧ mulK a' a = idK then
    ⟨toMatK a, toMatK a', by rw [← toMatK_mulK, h.1, toMatK_idK],
      by rw [← toMatK_mulK, h.2, toMatK_idK]⟩
  else 1

@[expose] def Rep (k : ℕ) (x : GL12) : Prop := toMatK k = (x : Mat12)

@[expose] def invPair (a a' : ℕ) : Bool := mulK a a' == idK && mulK a' a == idK

theorem rep_glOf {a a' : ℕ} (h : invPair a a' = true) : Rep a (glOf a a') := by
  simp only [invPair, Bool.and_eq_true, beq_iff_eq] at h
  simp [Rep, glOf, h]

theorem rep_glOf_inv {a a' : ℕ} (h : invPair a a' = true) : Rep a' (glOf a a')⁻¹ := by
  simp only [invPair, Bool.and_eq_true, beq_iff_eq] at h
  simp [Rep, glOf, h]

theorem rep_one : Rep idK 1 := toMatK_idK

theorem Rep.mul {a b : ℕ} {x y : GL12} (ha : Rep a x) (hb : Rep b y) : Rep (mulK a b) (x * y) := by
  rw [Rep, toMatK_mulK, ha, hb, Units.val_mul]

theorem Rep.pow {a : ℕ} {x : GL12} (ha : Rep a x) (n : ℕ) : Rep (powK a n) (x ^ n) := by
  rw [Rep, toMatK_powK, ha, Units.val_pow_eq_pow_val]

theorem Rep.unique {k : ℕ} {x y : GL12} (hx : Rep k x) (hy : Rep k y) : x = y :=
  Units.ext (hx.symm.trans hy)

theorem Rep.key_unique {a b : ℕ} {x : GL12} (ha : Rep a x) (hb : Rep b x) (ha' : a < 2 ^ 144)
    (hb' : b < 2 ^ 144) : a = b :=
  eq_of_toMatK_eq ha' hb' (ha.trans hb.symm)

@[expose] def stepK (R : Array ℕ) (ins : ℕ × ℕ × ℕ) : Array ℕ :=
  R.push (if ins.1 = 0 then mulK (R.getD ins.2.1 idK) (R.getD ins.2.2 idK)
    else powK (R.getD ins.2.1 idK) ins.2.2)

@[expose] def runK (gens : Array ℕ) (prog : List (ℕ × ℕ × ℕ)) : Array ℕ := prog.foldl stepK gens

@[expose] def stepG {M : Type*} [Monoid M] (R : Array M) (ins : ℕ × ℕ × ℕ) : Array M :=
  R.push (if ins.1 = 0 then R.getD ins.2.1 1 * R.getD ins.2.2 1 else R.getD ins.2.1 1 ^ ins.2.2)

@[expose] def runG {M : Type*} [Monoid M] (gens : Array M) (prog : List (ℕ × ℕ × ℕ)) : Array M :=
  prog.foldl stepG gens

theorem getD_push {α : Type*} (xs : Array α) (x : α) (i : ℕ) (d : α) :
    (xs.push x).getD i d = if i = xs.size then x else xs.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.getD_eq_getD_getElem?]
  split_ifs <;> rfl

theorem runK_rep : ∀ (prog : List (ℕ × ℕ × ℕ)) (gK : Array ℕ) (gG : Array GL12),
    gK.size = gG.size → (∀ i, Rep (gK.getD i idK) (gG.getD i 1)) →
      ∀ i, Rep ((runK gK prog).getD i idK) ((runG gG prog).getD i 1)
  | [], _, _, _, h => h
  | ins :: prog, gK, gG, hs, h => by
    refine runK_rep prog (stepK gK ins) (stepG gG ins) (by simp [stepK, stepG, hs]) fun i => ?_
    rw [stepK, stepG, getD_push, getD_push, hs]
    split_ifs with h1 h2
    · exact (h _).mul (h _)
    · exact (h _).pow _
    · exact h i

theorem runG_mem {M : Type*} [Group M] (S : Subgroup M) : ∀ (prog : List (ℕ × ℕ × ℕ))
    (gG : Array M), (∀ i, gG.getD i 1 ∈ S) → ∀ i, (runG gG prog).getD i 1 ∈ S
  | [], _, h => h
  | ins :: prog, gG, h => by
    refine runG_mem S prog (stepG gG ins) fun i => ?_
    rw [stepG, getD_push]
    split_ifs
    · exact S.mul_mem (h _) (h _)
    · exact S.pow_mem (h _) _
    · exact h i

theorem runK_lt : ∀ (prog : List (ℕ × ℕ × ℕ)) (gK : Array ℕ), (∀ i, gK.getD i idK < 2 ^ 144) →
    ∀ i, (runK gK prog).getD i idK < 2 ^ 144
  | [], _, h => h
  | ins :: prog, gK, h => by
    refine runK_lt prog (stepK gK ins) fun i => ?_
    rw [stepK, getD_push]
    split_ifs
    · exact mulK_lt _ _
    · exact powK_lt _ _
    · exact h i

@[expose] def tab (g : ℕ) : Array ℕ := Array.ofFn (n := 4096) fun a => rowMul 12 a (rowsOf g)

@[expose] def mulT (T : Array ℕ) (x : ℕ) : ℕ :=
  keyOf (Array.ofFn (n := 12) fun i => T.getD ((x >>> (12 * (i : ℕ))) % 4096) 0)

theorem tab_getD (g : ℕ) {a : ℕ} (ha : a < 4096) : (tab g).getD a 0 = rowMul 12 a (rowsOf g) := by
  unfold tab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [ha, ↓reduceDIte, Option.getD_some]

theorem getD_rowsOf (x : ℕ) {i : ℕ} (hi : i < 12) :
    (rowsOf x).getD i 0 = (x >>> (12 * i)) % 4096 := by
  unfold rowsOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]

theorem mulT_rows (g x : ℕ) :
    (Array.ofFn (n := 12) fun i => (tab g).getD ((x >>> (12 * (i : ℕ))) % 4096) 0) =
      bmul 12 12 (rowsOf x) (rowsOf g) := by
  unfold bmul
  apply Array.ext
  · simp
  · intro i hi1 _
    have hi : i < 12 := by simpa using hi1
    have hx : (x >>> (12 * i)) % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
    simp only [Array.getElem_ofFn]
    rw [tab_getD g hx, getD_rowsOf x hi]

theorem mulT_tab (g x : ℕ) : mulT (tab g) x = mulK x g := by
  rw [mulT, mulK, mulT_rows]

end CFSG.EvenSmallLie.OmegaEight.Stage2
