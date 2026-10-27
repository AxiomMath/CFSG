module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Pack
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def IsXorLin (f : ℕ → ℕ) : Prop := ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem IsXorLin.map_zero {f : ℕ → ℕ} (hf : IsXorLin f) : f 0 = 0 := by
  have h := hf 0 0
  rw [Nat.xor_self] at h
  have : f 0 ^^^ f 0 = 0 := Nat.xor_self _
  rw [← h] at this
  exact this

theorem xor_log2_lt {m : ℕ} (hm : m ≠ 0) : m ^^^ 2 ^ Nat.log2 m < m := by
  have hle : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le hm
  have hlt : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  refine lt_of_lt_of_le (Nat.lt_pow_two_of_testBit _ fun i hi => ?_) hle
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.eq_or_lt_of_le hi with h | h
  · subst h
    rw [Nat.testBit_log2 hm]
    simp
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) h))]
    simp [show Nat.log2 m ≠ i by omega]

theorem eq_self_of_isXorLin {f : ℕ → ℕ} (hf : IsXorLin f) {N : ℕ}
    (h : ∀ j < N, f (2 ^ j) = 2 ^ j) : ∀ m < 2 ^ N, f m = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h0 : m = 0
    · rw [h0, hf.map_zero]
    · set j := Nat.log2 m with hj
      have hjN : j < N := by
        rw [hj, Nat.log2_lt h0]
        exact hm
      have hlt : m ^^^ 2 ^ j < m := hj ▸ xor_log2_lt h0
      have e : m = (m ^^^ 2 ^ j) ^^^ 2 ^ j := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [e, hf, ih _ hlt (hlt.trans hm), h j hjN]

theorem IsXorLin.xor {f g : ℕ → ℕ} (hf : IsXorLin f) (hg : IsXorLin g) :
    IsXorLin fun m => f m ^^^ g m := by
  intro a b
  simp only [hf a b, hg a b]
  rw [Nat.xor_assoc, Nat.xor_assoc, ← Nat.xor_assoc (g a) (f b), Nat.xor_comm (g a) (f b),
    Nat.xor_assoc]

theorem IsXorLin.comp {f g : ℕ → ℕ} (hf : IsXorLin f) (hg : IsXorLin g) :
    IsXorLin fun m => f (g m) := by
  intro a b
  simp only [hg a b]
  exact hf _ _

@[expose] def linComb : List ℕ → ℕ → ℕ
  | [], _ => 0
  | q :: qs, v => (if v.testBit 0 then q else 0) ^^^ linComb qs (v / 2)

theorem isXorLin_linComb : ∀ qs : List ℕ, IsXorLin (linComb qs)
  | [] => fun _ _ => by simp [linComb]
  | q :: qs => fun a b => by
    simp only [linComb, Nat.testBit_xor, Nat.xor_div_two, isXorLin_linComb qs (a / 2) (b / 2)]
    cases a.testBit 0 <;> cases b.testBit 0 <;>
      simp only [Bool.bne_true, Bool.bne_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_xor] <;>
      (apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
       cases Nat.testBit q i <;> cases Nat.testBit (linComb qs (a / 2)) i <;>
         cases Nat.testBit (linComb qs (b / 2)) i <;> rfl)

theorem linComb_zero (qs : List ℕ) : linComb qs 0 = 0 := (isXorLin_linComb qs).map_zero

@[expose] def freeBits : List ℕ → ℕ → ℕ
  | [], _ => 0
  | f :: fs, m => Nat.bit (m.testBit f) (freeBits fs m)

theorem isXorLin_freeBits : ∀ fs : List ℕ, IsXorLin (freeBits fs)
  | [] => fun _ _ => by simp [freeBits]
  | f :: fs => fun a b => by
    simp only [freeBits, Nat.testBit_xor, isXorLin_freeBits fs a b, Nat.xor_bit]

theorem freeBits_lt : ∀ (fs : List ℕ) (m : ℕ), freeBits fs m < 2 ^ fs.length
  | [], _ => by simp [freeBits]
  | f :: fs, m => by
    have h := freeBits_lt fs m
    rw [freeBits, Nat.bit_val, List.length_cons, pow_succ]
    cases m.testBit f <;> simp <;> omega

theorem toMatK_xor (a b : ℕ) : toMatK (a ^^^ b) = toMatK a + toMatK b := by
  ext i j
  simp [toMatK, Nat.testBit_xor, bz_xor]

theorem mulK_xor_right (p a b : ℕ) : mulK p (a ^^^ b) = mulK p a ^^^ mulK p b := by
  apply eq_of_toMatK_eq (mulK_lt _ _) (Nat.xor_lt_two_pow (mulK_lt _ _) (mulK_lt _ _))
  rw [toMatK_mulK, toMatK_xor, toMatK_xor, toMatK_mulK, toMatK_mulK, mul_add]

theorem mulK_xor_left (a b q : ℕ) : mulK (a ^^^ b) q = mulK a q ^^^ mulK b q := by
  apply eq_of_toMatK_eq (mulK_lt _ _) (Nat.xor_lt_two_pow (mulK_lt _ _) (mulK_lt _ _))
  rw [toMatK_mulK, toMatK_xor, toMatK_xor, toMatK_mulK, toMatK_mulK, add_mul]

@[expose] def conPart : List (ℕ × ℕ) → List (List ℕ) → ℕ → ℕ
  | c :: cs, q :: qs, m => linComb q (mulK c.1 m ^^^ mulK m c.2) ^^^ conPart cs qs m
  | _, _, _ => 0

theorem isXorLin_conPart : ∀ (cs : List (ℕ × ℕ)) (qs : List (List ℕ)), IsXorLin (conPart cs qs)
  | c :: cs, q :: qs => by
    refine IsXorLin.xor (f := fun m => linComb q (mulK c.1 m ^^^ mulK m c.2)) ?_
      (isXorLin_conPart cs qs)
    refine (isXorLin_linComb q).comp fun a b => ?_
    rw [mulK_xor_right, mulK_xor_left]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases (mulK c.1 a).testBit i <;> cases (mulK c.1 b).testBit i <;>
      cases (mulK a c.2).testBit i <;> cases (mulK b c.2).testBit i <;> rfl
  | [], _ => fun _ _ => by simp [conPart]
  | _ :: _, [] => fun _ _ => by simp [conPart]

theorem conPart_eq_zero : ∀ (cs : List (ℕ × ℕ)) (qs : List (List ℕ)) {m : ℕ},
    (∀ c ∈ cs, mulK c.1 m = mulK m c.2) → conPart cs qs m = 0
  | c :: cs, q :: qs, m, h => by
    rw [conPart, h c List.mem_cons_self, Nat.xor_self, linComb_zero, Nat.zero_xor]
    exact conPart_eq_zero cs qs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
  | [], _, _, _ => by simp [conPart]
  | _ :: _, [], _, _ => by simp [conPart]

@[expose] def linRec (cons : List (ℕ × ℕ)) (qc : List (List ℕ)) (qf fs : List ℕ) (m : ℕ) : ℕ :=
  conPart cons qc m ^^^ linComb qf (freeBits fs m)

@[expose] def linCheckWith (cons : List (ℕ × ℕ)) (qc : List (List ℕ)) (qf fs : List ℕ) : Bool :=
  (List.range 144).all fun j => linRec cons qc qf fs (2 ^ j) == 2 ^ j

theorem eq_linComb_of_linCheckWith {cons : List (ℕ × ℕ)} {qc : List (List ℕ)} {qf fs : List ℕ}
    (h : linCheckWith cons qc qf fs = true) {m : ℕ} (hm : m < 2 ^ 144)
    (hsol : ∀ c ∈ cons, mulK c.1 m = mulK m c.2) : m = linComb qf (freeBits fs m) := by
  have hlin : IsXorLin (linRec cons qc qf fs) :=
    (isXorLin_conPart cons qc).xor ((isXorLin_linComb qf).comp (isXorLin_freeBits fs))
  have hj : ∀ j < 144, linRec cons qc qf fs (2 ^ j) = 2 ^ j := by
    intro j hj
    simp only [linCheckWith, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact h j hj
  have e := eq_self_of_isXorLin hlin hj m hm
  rw [linRec, conPart_eq_zero cons qc hsol, Nat.zero_xor] at e
  exact e.symm

@[expose] def conCol : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | c :: cs, k, j => ((mulK c.1 (2 ^ j) ^^^ mulK (2 ^ j) c.2) <<< (144 * k)) ||| conCol cs (k + 1) j

@[expose] def linSolve (cons : List (ℕ × ℕ)) : List (List ℕ) × List ℕ × List ℕ := Id.run do
  let K := cons.length
  let mut piv : Array (Option (ℕ × ℕ)) := Array.replicate (144 * K) none
  let mut fs : Array ℕ := #[]
  let mut qf : Array ℕ := #[]
  for j in [0:144] do
    let mut v := conCol cons 0 j
    let mut c := 2 ^ j
    let mut done := false
    for _ in [0:144 * K + 1] do
      if !done then
        if v == 0 then
          fs := fs.push j
          qf := qf.push c
          done := true
        else
          let h := Nat.log2 v
          match piv.getD h none with
          | some (pv, pc) =>
            v := v ^^^ pv
            c := c ^^^ pc
          | none =>
            piv := piv.set! h (some (v, c))
            done := true
  let mut q : Array ℕ := Array.replicate (144 * K) 0
  for i in [0:144 * K] do
    match piv.getD i none with
    | some (pv, pc) =>
      let rest := pv ^^^ 2 ^ i
      let mut acc := pc
      for b in [0:i] do
        if rest.testBit b then
          acc := acc ^^^ q.getD b 0
      q := q.set! i acc
    | none => pure ()
  let qc := (List.range K).map fun k => (List.range 144).map fun i => q.getD (144 * k + i) 0
  return (qc, qf.toList, fs.toList)

@[expose] def linBasis (cons : List (ℕ × ℕ)) : List ℕ := (linSolve cons).2.1

@[expose] def linFree (cons : List (ℕ × ℕ)) : List ℕ := (linSolve cons).2.2

@[expose] def linCheck (cons : List (ℕ × ℕ)) : Bool :=
  linCheckWith cons (linSolve cons).1 (linBasis cons) (linFree cons)

theorem eq_linComb_of_linCheck {cons : List (ℕ × ℕ)} (h : linCheck cons = true) {m : ℕ}
    (hm : m < 2 ^ 144) (hsol : ∀ c ∈ cons, mulK c.1 m = mulK m c.2) :
    m = linComb (linBasis cons) (freeBits (linFree cons) m) :=
  eq_linComb_of_linCheckWith h hm hsol

@[expose] def spanAll (qf : List ℕ) (d : ℕ) (P : ℕ → Bool) : Bool :=
  (List.range (2 ^ d)).all fun c => P (linComb qf c)

theorem forall_of_linCheck {cons : List (ℕ × ℕ)} (h : linCheck cons = true) {P : ℕ → Bool}
    (hP : spanAll (linBasis cons) (linFree cons).length P = true) {m : ℕ} (hm : m < 2 ^ 144)
    (hsol : ∀ c ∈ cons, mulK c.1 m = mulK m c.2) : P m = true := by
  rw [eq_linComb_of_linCheck h hm hsol]
  simp only [spanAll, List.all_eq_true, List.mem_range] at hP
  exact hP _ (freeBits_lt _ _)

end CFSG.EvenSmallLie.OmegaEight.Stage2
