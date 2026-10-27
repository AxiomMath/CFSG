module

public import CFSG.GH74.M12.HypCoreInputs
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.GH74.M12.Hyp

@[expose] def tbl (σ : Equiv.Perm (Fin 12)) : List ℕ := List.ofFn fun i : Fin 12 => (σ i).val

theorem tbl_length (σ : Equiv.Perm (Fin 12)) : (tbl σ).length = 12 := by
  unfold tbl; rw [List.length_ofFn]

theorem tbl_getElem? (σ : Equiv.Perm (Fin 12)) (n : ℕ) :
    (tbl σ)[n]? = if h : n < 12 then some (σ ⟨n, h⟩).val else none := by
  unfold tbl
  rw [List.getElem?_ofFn]

theorem tbl_getD (σ : Equiv.Perm (Fin 12)) (i : Fin 12) : (tbl σ).getD i.val 0 = (σ i).val := by
  rw [List.getD_eq_getElem?_getD, tbl_getElem?]
  simp [i.isLt]

theorem tbl_getD_of_lt (σ : Equiv.Perm (Fin 12)) {n : ℕ} (hn : n < 12) :
    (tbl σ).getD n 0 = (σ ⟨n, hn⟩).val :=
  tbl_getD σ ⟨n, hn⟩

theorem tbl_injective : Function.Injective tbl := by
  intro σ τ h
  ext i
  have h1 := tbl_getD σ i
  have h2 := tbl_getD τ i
  rw [h] at h1
  rw [← h1, h2]

theorem tbl_mul (σ τ : Equiv.Perm (Fin 12)) : tbl (σ * τ) = tmul (tbl σ) (tbl τ) := by
  apply List.ext_getElem?
  intro n
  rw [tbl_getElem?]
  unfold tmul
  rw [List.getElem?_map, tbl_getElem?]
  by_cases hn : n < 12
  · simp only [hn, ↓reduceDIte, Option.map_some]
    rw [Equiv.Perm.coe_mul, Function.comp_apply]
    congr 1
    exact (tbl_getD σ (τ ⟨n, hn⟩)).symm
  · simp [hn]

theorem tbl_one : tbl (1 : Equiv.Perm (Fin 12)) = tid := by
  apply List.ext_getElem?
  intro n
  rw [tbl_getElem?]
  unfold tid
  by_cases hn : n < 12
  · simp [hn]
  · simp [hn]

theorem tbl_inv (σ : Equiv.Perm (Fin 12)) : tbl σ⁻¹ = tinv (tbl σ) := by
  apply List.ext_getElem?
  intro n
  rw [tbl_getElem?]
  unfold tinv
  rw [List.getElem?_map]
  by_cases hn : n < 12
  · simp only [hn, ↓reduceDIte, List.getElem?_range, Option.map_some]
    congr 1
    have hnd : (tbl σ).Nodup := by
      unfold tbl
      rw [List.nodup_ofFn]
      intro i j hij
      exact σ.injective (Fin.ext hij)
    have hlt : (σ⁻¹ ⟨n, hn⟩).val < (tbl σ).length := by
      rw [tbl_length]; exact (σ⁻¹ ⟨n, hn⟩).isLt
    have hget : (tbl σ)[(σ⁻¹ ⟨n, hn⟩).val] = n := by
      have := tbl_getD σ (σ⁻¹ ⟨n, hn⟩)
      rw [List.getD_eq_getElem _ _ hlt] at this
      rw [this]
      simp
    have := List.Nodup.idxOf_getElem hnd _ hlt
    rw [hget] at this
    exact this.symm
  · simp [hn]

theorem tbl_pow (σ : Equiv.Perm (Fin 12)) (n : ℕ) : tbl (σ ^ n) = tpow (tbl σ) n := by
  induction n with
  | zero => rw [pow_zero, tbl_one]; rfl
  | succ n ih => rw [pow_succ', tbl_mul, ih]; rfl

theorem tbl_eq_iff {σ τ : Equiv.Perm (Fin 12)} : tbl σ = tbl τ ↔ σ = τ :=
  tbl_injective.eq_iff

theorem tbl_take_five {σ τ : Equiv.Perm (Fin 12)} (h : (tbl σ).take 5 = (tbl τ).take 5) :
    ∀ i : Fin 12, i.val < 5 → σ i = τ i := by
  intro i hi
  have key : ∀ ρ : Equiv.Perm (Fin 12), ((tbl ρ).take 5).getD i.val 0 = (ρ i).val := by
    intro ρ
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]
    exact tbl_getD ρ i
  have := congrArg (fun l : List ℕ => l.getD i.val 0) h
  simp only [key] at this
  exact Fin.ext this

end CFSG.GH74.M12.Hyp
