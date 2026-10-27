module

public import Certificates.Data.Kernel.Fi23Pump.Defs
public import CFSG.Certificates.Kernel.Fi23Q.WordSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KS.Fi23Pump

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Fi23R CFSG.KC.Fi23Pump CFSG.KS.Raw.Orb

theorem yK_spec {G : Nat → Nat} {y t : List Nat} (h : yK G y t = true) :
    (∀ b < 6, wv G (powW 5 y) b = wv G [] b) ∧ ¬ (∀ b < 6, wv G y b = wv G [] b) ∧
      ∀ b < 6, wv G (y ++ t) b = wv G (t ++ y) b := by
  unfold yK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨eqH_spec h1, fun hy => ?_, eqH_spec h3⟩
  have : eqH G y [] = true := by
    unfold eqH
    refine allN_iff.2 fun b hb => ?_
    rw [hy b hb]
    exact Nat.beq_refl _
  rw [h2] at this
  exact Bool.false_ne_true this

theorem rowK_spec {G : Nat → Nat} {u v : List Nat} {P N r i : Nat} (h : rowK G u v P N r i = true) :
    ptE (recP P i) < 31671 ∧ (depE (recP P i) = 0 → ptE (recP P i) = r) ∧
      (depE (recP P i) ≠ 0 → ∃ j < N, depE (recP P j) + 1 = depE (recP P i) ∧
        (ptE (recP P i) = wv G u (ptE (recP P j)) ∨ ptE (recP P i) = wv G v (ptE (recP P j)))) := by
  unfold rowK at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.blt_eq.mp h1, fun hd => ?_, fun hd => ?_⟩
  · rw [if_pos (by rw [hd]; rfl)] at h2
    exact Nat.eq_of_beq_eq_true h2
  · rw [if_neg (fun h' => hd (Nat.eq_of_beq_eq_true h')), strictB_eq, strictB_eq] at h2
    unfold rowE at h2
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h2
    obtain ⟨hj, hdep, hw⟩ := h2
    refine ⟨_, Nat.blt_eq.mp hj, Nat.eq_of_beq_eq_true hdep, ?_⟩
    have hw' := (Nat.eq_of_beq_eq_true hw).symm
    unfold genW at hw'
    rw [nIf_eq] at hw'
    split_ifs at hw'
    · exact Or.inl hw'
    · exact Or.inr hw'

theorem orbK_spec {G : Nat → Nat} {u v : List Nat} {P N r : Nat} (h : orbK G u v P N r = true)
    (R : Nat → Prop) (hr : R r) (hu : ∀ q < 31671, R q → R (wv G u q))
    (hv : ∀ q < 31671, R q → R (wv G v q)) :
    (∀ i < N, ptE (recP P i) < 31671 ∧ R (ptE (recP P i))) ∧
      ∀ i j, i < j → j < N → ptE (recP P i) < ptE (recP P j) := by
  unfold orbK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hrow, hinc⟩ := h
  have hrow' := fun i hi => rowK_spec (allN_iff.1 hrow i hi)
  have key : ∀ d, ∀ i < N, depE (recP P i) = d → R (ptE (recP P i)) := by
    intro d
    induction d with
    | zero => intro i hi hd; rw [(hrow' i hi).2.1 hd]; exact hr
    | succ d ih =>
      intro i hi hd
      obtain ⟨j, hj, hdj, hw⟩ := (hrow' i hi).2.2 (by omega)
      have hRj := ih j hj (by omega)
      have hlt := (hrow' j hj).1
      rcases hw with e | e
      · rw [e]; exact hu _ hlt hRj
      · rw [e]; exact hv _ hlt hRj
  refine ⟨fun i hi => ⟨(hrow' i hi).1, key _ i hi rfl⟩, ?_⟩
  have hs : ∀ i, i + 1 < N → ptE (recP P i) < ptE (recP P (i + 1)) := fun i hi =>
    Nat.blt_eq.mp (allN_iff.1 hinc i (by change i < N - 1; omega))
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => exact hs i hj
  | succ k hk ih => exact lt_trans (ih (by omega)) (hs k hj)

end CFSG.KS.Fi23Pump

end
