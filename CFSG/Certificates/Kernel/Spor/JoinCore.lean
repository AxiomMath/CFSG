module

public import Certificates.Data.Kernel.Spor.Join
public import Certificates.Data.Kernel.Misc.HexFlat
public import Certificates.Data.CFSGNative.SmallOddCore.Check
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.HeFixKFix
public import CFSG.Certificates.Kernel.Spor.RawDefs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.Join

open CFSG.KS.Raw CFSG.KC.Enum

theorem testBit_foldr {C j b : Nat} {Fc : Nat → Nat} (m : Nat)
    (hlt : ∀ i < m, Fc (C * j + i) < 2 ^ b) (s p : Nat) :
    ((List.range m).foldr (fun i s => Nat.lor s (Nat.shiftLeft (Fc (Nat.add (Nat.mul C j) i))
      (Nat.mul b i))) s).testBit p =
      (s.testBit p || (decide (p < b * m) && (Fc (C * j + p / b)).testBit (p % b))) := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
      ih (fun i hi => hlt i (by omega))]
    change ((s ||| ((Fc (C * j + m)) <<< (b * m))).testBit p ||
      (decide (p < b * m) && (Fc (C * j + p / b)).testBit (p % b))) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge p (b * m) with h1 | h1
    · have h2 : p < b * (m + 1) := by nlinarith
      simp [h1, h2, show ¬ (b * m ≤ p) by omega]
    · rcases Nat.lt_or_ge p (b * (m + 1)) with h2 | h2
      · have hb : 0 < b := by
          rcases Nat.eq_zero_or_pos b with h | h
          · subst h
            simp at h2
          · exact h
        have hq : p / b = m := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
        have hr : p % b = p - b * m := by
          have := Nat.div_add_mod p b
          rw [hq] at this
          omega
        simp [h1, h2, show ¬ p < b * m by omega, hq, hr, mul_comm]
      · have hz : (Fc (C * j + m)).testBit (p - b * m) = false := by
          apply Nat.testBit_lt_two_pow
          calc Fc (C * j + m) < 2 ^ b := hlt m (by omega)
            _ ≤ 2 ^ (p - b * m) := Nat.pow_le_pow_right (by norm_num) (by
              have : b * (m + 1) = b * m + b := by ring
              omega)
        simp [h1, show ¬ p < b * (m + 1) by omega, show ¬ p < b * m by omega, hz]

theorem pg_joinOf {c n₀ w j i : Nat} (hn : 0 < n₀) {Fc : Nat → Nat}
    (hlt : ∀ t < c, Fc (c * j + t) < 2 ^ (w * n₀)) (hi : i < c * n₀) :
    pg w (mask w) (joinOf c (w * n₀) Fc j) i = pg w (mask w) (Fc (c * j + i / n₀)) (i % n₀) := by
  rw [CFSG.KC.Pack.mask_eq, CFSG.KC.Pack.pg_eq, CFSG.KC.Pack.pg_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hk : k < w
  · have hw : 0 < w := by omega
    simp only [hk, decide_true, Bool.true_and]
    unfold joinOf
    rw [CFSG.KS.Raw.Orb.foldN_eq, testBit_foldr c hlt]
    have hp : k + w * i < w * n₀ * c := by nlinarith
    have hdiv : (k + w * i) / (w * n₀) = i / n₀ := by
      have e : k + w * i = w * n₀ * (i / n₀) + (k + w * (i % n₀)) := by
        have := Nat.div_add_mod i n₀
        nlinarith
      rw [e, Nat.mul_add_div (by positivity)]
      have : k + w * (i % n₀) < w * n₀ := by
        have := Nat.mod_lt i hn
        nlinarith
      rw [Nat.div_eq_of_lt this, add_zero]
    have hmod : (k + w * i) % (w * n₀) = k + w * (i % n₀) := by
      have e : k + w * i = w * n₀ * (i / n₀) + (k + w * (i % n₀)) := by
        have := Nat.div_add_mod i n₀
        nlinarith
      rw [e, Nat.mul_add_mod]
      apply Nat.mod_eq_of_lt
      have := Nat.mod_lt i hn
      nlinarith
    simp [hp, hdiv, hmod, Nat.zero_testBit, add_comm]
  · simp [hk]

theorem hexT_get {d m off : Nat} {s : String} {i : Nat} (hi : i < m) :
    (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.Native.hexT d m off s))[i]! =
      (UInt32.ofNat (CFSG.Sporadic.SmallOddCore.Native.hexNum s.toUTF8 (d * (off + i)) d)).toNat := by
  have hs : i < (CFSG.Sporadic.SmallOddCore.Native.natArr
      (CFSG.Sporadic.SmallOddCore.Native.hexT d m off s)).size := by
    simp [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT, hi]
  rw [getElem!_pos _ i hs]
  simp [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT]

theorem hexTable_get {d m off : Nat} {s : String} {i : Nat} (hi : i < m) :
    (CFSG.Monster.B.Co2.Native.hexTable d m off s)[i]! =
      CFSG.Monster.B.Co2.Native.hexAt s.toUTF8 (d * (off + i)) d := by
  have hs : i < (CFSG.Monster.B.Co2.Native.hexTable d m off s).size := by
    simp [CFSG.Monster.B.Co2.Native.hexTable, hi]
  rw [getElem!_pos _ i hs]
  simp [CFSG.Monster.B.Co2.Native.hexTable]

theorem n₀_pos {cs : List Char} {d n₀ w N : Nat} {Fc : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d n₀ w N Fc = true) : 0 < n₀ := by
  unfold CFSG.KC.Misc.HexFlat.hexFlat at hx
  simp only [bAnd_iff] at hx
  exact Nat.blt_eq.mp hx.2.1

theorem join_parts {c n₀ w N j : Nat} {Fc F : Nat → Nat}
    (hj : joinK c (w * n₀) Fc F N = true) (hjN : j < N) :
    (∀ t < c, Fc (c * j + t) < 2 ^ (w * n₀)) ∧ F j = joinOf c (w * n₀) Fc j := by
  have hJ := allN_spec hj j hjN
  obtain ⟨hJ1, hJ2⟩ := (bAnd_iff _ _).1 hJ
  refine ⟨fun t ht => ?_, Nat.eq_of_beq_eq_true hJ2⟩
  have h := Nat.eq_of_beq_eq_true (allN_spec hJ1 t ht)
  change Fc (c * j + t) >>> (w * n₀) = 0 at h
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (by positivity)).1 h

theorem index_split {c n₀ j i : Nat} (hn : 0 < n₀) :
    n₀ * (c * j + i / n₀) + i % n₀ = c * n₀ * j + i := by
  have := Nat.div_add_mod i n₀
  nlinarith

theorem chunk_index_lt {c n₀ N j i : Nat} (hn : 0 < n₀) (hjN : j < N) (hi : i < c * n₀) :
    c * j + i / n₀ < c * N := by
  have : i / n₀ < c := (Nat.div_lt_iff_lt_mul hn).2 hi
  have : j + 1 ≤ N := hjN
  nlinarith

theorem hexTable_join_core {cs : List Char} {d n₀ w c N : Nat} {Fc F : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d n₀ w (c * N) Fc = true)
    (hj : joinK c (w * n₀) Fc F N = true) :
    ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d (c * n₀) (c * n₀ * j) (String.ofList cs) =
      unpack (c * n₀) w (F j) := by
  intro j hjN
  have hn := n₀_pos hx
  have hch := CFSG.KC.Misc.HexFlat.hexTable_sound hx
  obtain ⟨hlt, hF⟩ := join_parts hj hjN
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, unpack]
  · intro i h1 h2
    have hi : i < c * n₀ := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    have hc := hch (c * j + i / n₀) (chunk_index_lt hn hjN hi)
    have hr : i % n₀ < n₀ := Nat.mod_lt _ hn
    have e1 : (CFSG.Monster.B.Co2.Native.hexTable d n₀ (n₀ * (c * j + i / n₀))
        (String.ofList cs))[i % n₀]! = (unpack n₀ w (Fc (c * j + i / n₀)))[i % n₀]! := by
      rw [hc]
    rw [hexTable_get hr, CFSG.KC.HeFixK.unpack_getElem! hr] at e1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, hexTable_get hi,
      CFSG.KC.HeFixK.unpack_getElem! hi, hF, pg_joinOf hn hlt hi, ← e1, index_split hn]

theorem hexT_join_core {cs : List Char} {d n₀ w c N : Nat} {Fc F : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d n₀ w (c * N) Fc = true)
    (hj : joinK c (w * n₀) Fc F N = true) (hw : w ≤ 32) :
    ∀ j < N, CFSG.Sporadic.SmallOddCore.Native.natArr
      (CFSG.Sporadic.SmallOddCore.Native.hexT d (c * n₀) (c * n₀ * j) (String.ofList cs)) =
        unpack (c * n₀) w (F j) := by
  intro j hjN
  have hn := n₀_pos hx
  have hch := CFSG.KC.Misc.HexFlat.hexT_sound hx hw
  obtain ⟨hlt, hF⟩ := join_parts hj hjN
  apply Array.ext
  · simp [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT, unpack]
  · intro i h1 h2
    have hi : i < c * n₀ := by
      simpa [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.Sporadic.SmallOddCore.Native.hexT]
        using h1
    have hc := hch (c * j + i / n₀) (chunk_index_lt hn hjN hi)
    have hr : i % n₀ < n₀ := Nat.mod_lt _ hn
    have e1 : (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.Native.hexT d n₀
        (n₀ * (c * j + i / n₀)) (String.ofList cs)))[i % n₀]! =
        (unpack n₀ w (Fc (c * j + i / n₀)))[i % n₀]! := by rw [hc]
    rw [hexT_get hr, CFSG.KC.HeFixK.unpack_getElem! hr] at e1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, hexT_get hi,
      CFSG.KC.HeFixK.unpack_getElem! hi, hF, pg_joinOf hn hlt hi, ← e1, index_split hn]

end CFSG.KS.Join

end
