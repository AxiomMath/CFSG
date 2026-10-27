module

public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.CosetLog
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
public import Mathlib.Topology.Sheaves.Init

namespace CFSG.KC.CLog

open CFSG.KC.Enum CFSG.KS.PEnum

theorem sB' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bIfE' (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

public section

theorem clogK_slices {m nR NC NF SM k : Nat} {RL RN FD FS FW SD DT : Nat → Nat}
    (hn : NF ≤ 4000 * k)
    (hs : ∀ s < k, factSlK m nR NC SM NF RL RN FD FS FW SD DT (Nat.mul 4000 s) 4000 = true) :
    ∀ t < NF, factK m nR NC SM RL RN FD FS FW SD DT t = true := by
  intro t ht
  have h := CFSG.KS.allN_spec (hs (t / 4000) (by omega)) (t - 4000 * (t / 4000)) (by omega)
  simp only [sB', bIfE'] at h
  have e : Nat.add (Nat.mul 4000 (t / 4000)) (t - 4000 * (t / 4000)) = t := by
    change 4000 * (t / 4000) + (t - 4000 * (t / 4000)) = t
    omega
  have hb : Nat.blt t NF = true := by
    rw [Nat.blt_eq]
    exact ht
  rw [e, ite_eq_left hb] at h
  exact h

end

end CFSG.KC.CLog
