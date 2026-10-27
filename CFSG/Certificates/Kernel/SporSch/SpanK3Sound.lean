module

public import Certificates.Data.Kernel.SporSch.SpanK3
public import CFSG.Certificates.Kernel.SporSch.SpanKSound
public import Certificates.Data.Co2RowChk

public section

namespace CFSG.KS.SpanK

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative

theorem stepK3_eq {T0 T1 T2 : Array ℕ} {f0 f1 f2 : ℕ → ℕ}
    (h0 : ∀ a < 256, f0 a = vecMulN 8 T0 a) (h1 : ∀ a < 256, f1 a = vecMulN 8 T1 a)
    (h2 : ∀ a < 256, f2 a = vecMulN 8 T2 a) (S : ℕ) :
    stepK3 f0 f1 f2 S = spanStepL [T0, T1, T2] S := by
  have loop : ∀ n ≤ 256,
      Nat.rec (motive := fun _ => ℕ) S (fun a acc => CFSG.KC.Enum.strictN acc fun acc =>
        bif bitK S a then insK (insK (insK acc (f0 a)) (f1 a)) (f2 a) else acc) n =
      Nat.rec (motive := fun _ => ℕ) S (fun k acc =>
        if S.testBit k = true then
          spanIns (spanIns (spanIns acc (vecMulN 8 T0 k)) (vecMulN 8 T1 k)) (vecMulN 8 T2 k)
        else acc) n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      change CFSG.KC.Enum.strictN _ (fun acc =>
          bif bitK S n then insK (insK (insK acc (f0 n)) (f1 n)) (f2 n) else acc) =
        (if S.testBit n = true then
          spanIns (spanIns (spanIns _ (vecMulN 8 T0 n)) (vecMulN 8 T1 n)) (vecMulN 8 T2 n)
        else _)
      rw [strictN_eq, ih (by omega), bitK_eq, insK_eq, insK_eq, insK_eq,
        h0 n (by omega), h1 n (by omega), h2 n (by omega)]
      cases S.testBit n <;> rfl
  unfold stepK3 spanStepL
  simp only [List.foldl_cons, List.foldl_nil]
  rewrite [foldl_range_eq_rec]
  exact loop 256 le_rfl

theorem iterK3_eq {T0 T1 T2 : Array ℕ} {f0 f1 f2 : ℕ → ℕ}
    (h0 : ∀ a < 256, f0 a = vecMulN 8 T0 a) (h1 : ∀ a < 256, f1 a = vecMulN 8 T1 a)
    (h2 : ∀ a < 256, f2 a = vecMulN 8 T2 a) :
    ∀ n S, iterK3 f0 f1 f2 n S = spanIterL [T0, T1, T2] n S
  | 0, _ => rfl
  | n + 1, S => by
    change CFSG.KC.Enum.strictN (stepK3 f0 f1 f2 S) (iterK3 f0 f1 f2 n) =
      spanIterL [T0, T1, T2] n (spanStepL [T0, T1, T2] S)
    rw [strictN_eq, stepK3_eq h0 h1 h2, iterK3_eq h0 h1 h2 n]

end CFSG.KS.SpanK

end
