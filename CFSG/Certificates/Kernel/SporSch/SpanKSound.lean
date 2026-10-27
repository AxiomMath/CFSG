module

public import Certificates.Data.Kernel.SporSch.SpanK
public import CFSG.Sporadic.Co2Schreier.QCheckInputs

public section

namespace CFSG.KS.SpanK

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.SmallF2.Native

theorem bitK_eq (S a : ℕ) : bitK S a = S.testBit a := CFSG.RankThree.Native.F2.beq_bit S a

theorem foldl_range_eq_rec {α : Type} (f : α → ℕ → α) (init : α) :
    ∀ n, (List.range n).foldl f init = Nat.rec (motive := fun _ => α) init (fun k acc => f acc k) n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_range_eq_rec f init n]
    rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem insLoop (S x : ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) S (fun a acc => CFSG.KC.Enum.strictN acc fun acc =>
      bif bitK S a then Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.xor a x)) else acc) n =
    Nat.rec (motive := fun _ => ℕ) S (fun k acc =>
      if S.testBit k = true then acc ||| 1 <<< (k ^^^ x) else acc) n
  | 0 => rfl
  | n + 1 => by
    change CFSG.KC.Enum.strictN _ (fun acc =>
        bif bitK S n then Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.xor n x)) else acc) =
      (if S.testBit n = true then _ ||| 1 <<< (n ^^^ x) else _)
    rw [strictN_eq, insLoop S x n, bitK_eq]
    cases S.testBit n <;> rfl

theorem insK_eq (S x : ℕ) : insK S x = spanIns S x := by
  unfold insK spanIns
  rewrite [bitK_eq, foldl_range_eq_rec]
  cases S.testBit x
  · rewrite [Bool.cond_false, ite_eq_right Bool.false_ne_true]
    exact insLoop S x 256
  · rfl

theorem stepK_eq {T0 T1 : Array ℕ} {f0 f1 : ℕ → ℕ} (h0 : ∀ a < 256, f0 a = vecMulN 8 T0 a)
    (h1 : ∀ a < 256, f1 a = vecMulN 8 T1 a) (S : ℕ) : stepK f0 f1 S = spanStep T0 T1 S := by
  have loop : ∀ n ≤ 256,
      Nat.rec (motive := fun _ => ℕ) S (fun a acc => CFSG.KC.Enum.strictN acc fun acc =>
        bif bitK S a then insK (insK acc (f0 a)) (f1 a) else acc) n =
      Nat.rec (motive := fun _ => ℕ) S (fun k acc =>
        if S.testBit k = true then spanIns (spanIns acc (vecMulN 8 T0 k)) (vecMulN 8 T1 k)
        else acc) n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      change CFSG.KC.Enum.strictN _ (fun acc =>
          bif bitK S n then insK (insK acc (f0 n)) (f1 n) else acc) =
        (if S.testBit n = true then spanIns (spanIns _ (vecMulN 8 T0 n)) (vecMulN 8 T1 n) else _)
      rw [strictN_eq, ih (by omega), bitK_eq, insK_eq, insK_eq,
        h0 n (by omega), h1 n (by omega)]
      cases S.testBit n <;> rfl
  unfold stepK spanStep
  rewrite [foldl_range_eq_rec]
  exact loop 256 le_rfl

theorem iterK_eq {T0 T1 : Array ℕ} {f0 f1 : ℕ → ℕ} (h0 : ∀ a < 256, f0 a = vecMulN 8 T0 a)
    (h1 : ∀ a < 256, f1 a = vecMulN 8 T1 a) : ∀ n S, iterK f0 f1 n S = spanIter T0 T1 n S
  | 0, _ => rfl
  | n + 1, S => by
    change CFSG.KC.Enum.strictN (stepK f0 f1 S) (iterK f0 f1 n) =
      spanIter T0 T1 n (spanStep T0 T1 S)
    rw [strictN_eq, stepK_eq h0 h1, iterK_eq h0 h1 n]

end CFSG.KS.SpanK

end
