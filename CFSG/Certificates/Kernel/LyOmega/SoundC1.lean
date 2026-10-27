module

public import Certificates.Data.Kernel.LyOmega.Chart
import all CFSG.Certificates.Kernel.LyOmega.SoundB1
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

public section

namespace CFSG.KS.LyOm.SC1

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop CFSG.KS.LyOm.SB1

private theorem bIf_eq' (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem nIf_eq' (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem shl6 (b j : ℕ) : Nat.add (Nat.shiftLeft b 6) j = 64 * b + j := by
  change b <<< 6 + j = 64 * b + j
  rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  omega

private theorem sumBelow_eq' (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have hgen : ∀ h, CFSG.KC.Loop.sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + CFSG.KC.Loop.sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      simp only [shl6, nIf_eq', Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem cRange_sound {C : BConsts} {KX PT WT GT WC : ℕ → ℕ} {nc n b₀ c : ℕ}
    (h : cRange C KX PT WT GT WC nc n b₀ c = true) :
    ∀ i, 64 * b₀ ≤ i → i < 64 * (b₀ + c) → i < n → cNode C KX PT WT GT WC nc n i = true := by
  intro i h1 h2 h3
  have key := allBelow_spec h (le_of_eq rfl) (i - 64 * b₀) (by change _ < 64 * c; omega)
  have e : Nat.add (Nat.shiftLeft b₀ 6) (i - 64 * b₀) = i := by
    rw [shl6]; omega
  dsimp only at key
  rw [e, bIf_eq', if_pos (blt_iff.2 h3)] at key
  exact key

theorem cSort_sound {KX PT SG : ℕ → ℕ} {n k₀ c : ℕ} (h : cSort KX PT SG n k₀ c = true) :
    ∀ k, k₀ ≤ k → k < k₀ + c → getRec SG 20 k < n ∧ getRec SG 20 (k + 1) < n ∧
      cKey KX PT (getRec SG 20 k) < cKey KX PT (getRec SG 20 (k + 1)) := by
  intro k hk1 hk2
  have hm : c ≤ 64 * (Nat.shiftRight c (nat_lit 6) + 1) := by
    rw [shr6]; omega
  have key := allBelow_spec h hm (k - k₀) (by omega)
  have e : Nat.add k₀ (k - k₀) = k := by change k₀ + (k - k₀) = k; omega
  dsimp only at key
  rw [e] at key
  simp only [letB_eq, bAnd_eq, Bool.and_eq_true, blt_iff, Nat.succ_eq_add_one] at key
  exact ⟨key.1, key.2.1, key.2.2⟩

theorem cFix_eq {C : BConsts} {KX PT XM : ℕ → ℕ} {n b₀ c : ℕ} :
    cFix C KX PT XM n b₀ c = ((Finset.Ico (64 * b₀) (64 * (b₀ + c))).filter fun i => i < n ∧
      sameSpanL C (getRec KX 9324 i) (bMul C (getRec KX 9324 i) (XM (chartOf (getRec PT 32 i)))) =
        true).card := by
  unfold cFix
  rw [sumBelow_eq' (Nat.mul 64 c) c _ (le_of_eq rfl), Finset.card_filter,
    Finset.sum_Ico_eq_sum_range, show 64 * (b₀ + c) - 64 * b₀ = Nat.mul 64 c by
      change _ = 64 * c; omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [shl6, nIf_eq', bAnd_eq, Bool.and_eq_true, blt_iff]

end CFSG.KS.LyOm.SC1

end
