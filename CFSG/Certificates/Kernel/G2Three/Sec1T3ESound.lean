module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3Sound
public import Certificates.Data.Kernel.G2Three.Sec1T3E
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

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop

theorem latSortK_step {L OR m : ℕ} (h : latSortK L OR m = true) (hm : m ≤ 448) {k : ℕ}
    (hk : k + 1 < m) : latKey L OR k < latKey L OR (k + 1) := by
  have := allBelow_spec h (by omega) k (by omega)
  have hb : Nat.blt (Nat.succ k) m = true := by rw [Nat.blt_eq]; exact hk
  rw [hb] at this
  exact Nat.blt_eq.mp this

theorem latSortK_lt {L OR m : ℕ} (h : latSortK L OR m = true) (hm : m ≤ 448) {k : ℕ} :
    ∀ d, k + d + 1 < m → latKey L OR k < latKey L OR (k + d + 1)
  | 0, hd => latSortK_step h hm hd
  | d + 1, hd => (latSortK_lt h hm d (by omega)).trans (latSortK_step h hm (k := k + d + 1) hd)

theorem latSort_inj {L OR m : ℕ} (h : latSortK L OR m = true) (ho : ordK L OR 0 m = true)
    (hm : m ≤ 448) : ∀ k < m, ∀ k' < m, latM L k = latM L k' → k = k' := by
  have key : ∀ k < m, ∀ k' < m, k < k' → latM L k ≠ latM L k' := by
    intro k hk k' hk' hlt he
    have h1 := latSortK_lt h hm (k := k) (k' - k - 1) (by omega)
    have e : k + (k' - k - 1) + 1 = k' := by omega
    rw [e] at h1
    have ho1 := ordK_spec ho hm k hk
    have ho2 := ordK_spec ho hm k' hk'
    have hk2 : latKey L OR k = latKey L OR k' := by
      change Nat.add (Nat.shiftLeft (ordAt OR k) 128) (latM L k) =
        Nat.add (Nat.shiftLeft (ordAt OR k') 128) (latM L k')
      rw [← ho1, ← ho2, he]
    omega
  intro k hk k' hk' he
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd he (key k hk k' hk' hlt)
  · exact heq
  · exact absurd he.symm (key k' hk' k hk hgt)

end CFSG.KC.G2Three.Sec1T3

end
