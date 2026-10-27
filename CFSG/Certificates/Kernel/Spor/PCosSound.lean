module

public import Certificates.Data.Kernel.Spor.PCos
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
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

namespace CFSG.KS.PCos

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb

variable {n w : ℕ}

theorem cosK_spec (hn : n < 2 ^ 32) {cnt jc kw kg X : ℕ} {T JT W G E : ℕ → ℕ}
    {x y v g : ℕ → Equiv.Perm (Fin n)} {x₀ : Equiv.Perm (Fin n)}
    (hx : ∀ q < cnt, PRep n w (T q) (x q)) (hy : ∀ j < jc, PRep n w (JT j) (y j))
    (hv : ∀ k < kw, PRep n w (W k) (v k)) (hg : ∀ c < kg, PRep n w (G c) (g c))
    (hX : PRep n w X x₀) (h : cosK n w (mask w) cnt T jc JT kw W kg G X E = true) :
    ∀ q < cnt, ∃ j < jc, (∃ k < kw, x q = v k * y j) ∨
      ∃ c < kg, x₀ * x q * y j * g c = g c * x q := by
  intro q hq
  have h1 := allN_iff.1 h q hq
  simp only [Orb.strictB_eq] at h1
  unfold cosPtK at h1
  simp only [Orb.strictB_eq] at h1
  rw [bAnd_eq, Bool.and_eq_true, bIf_eq] at h1
  obtain ⟨hj, h2⟩ := h1
  have hj' := Nat.blt_eq.mp hj
  refine ⟨_, hj', ?_⟩
  split_ifs at h2 with hk
  · have hk' := Nat.blt_eq.mp hk
    have h3 := prep_pcomp hn (hv _ hk') (hy _ hj')
    rw [← Nat.eq_of_beq_eq_true h2] at h3
    exact Or.inl ⟨_, hk', CFSG.KC.OrbGroup.prep_eq (hx q hq) h3⟩
  · rw [bAnd_eq, Bool.and_eq_true] at h2
    obtain ⟨hc, he⟩ := h2
    have hc' := Nat.blt_eq.mp hc
    have h3 := prep_pcomp hn (prep_pcomp hn (prep_pcomp hn hX (hx q hq)) (hy _ hj')) (hg _ hc')
    rw [Nat.eq_of_beq_eq_true he] at h3
    exact Or.inr ⟨_, hc', CFSG.KC.OrbGroup.prep_eq h3 (prep_pcomp hn (hg _ hc') (hx q hq))⟩

end CFSG.KS.PCos

end
