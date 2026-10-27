module

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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GF2Type.Smith1979.Case2.U43Grp

variable {X : Type} [Group X]

theorem conj_pow_mem {y : X} {S : Subgroup X} (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) {w : X}
    (hw : w ∈ S) (k : ℕ) : y ^ k * w * (y ^ k)⁻¹ ∈ S := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    have h := hyS _ ih
    have e : y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ = y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [← e]
    exact h

theorem conj_pow_eq {g w : X} (hg : g * w * g⁻¹ = w) (j : ℕ) : g ^ j * w * (g ^ j)⁻¹ = w := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : g ^ (j + 1) * w * (g ^ (j + 1))⁻¹ = g * (g ^ j * w * (g ^ j)⁻¹) * g⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [e, ih, hg]

theorem conj_fix_of_pow_fix {y : X} (hy : orderOf y = 7) {w : X} {d : ℕ} (hd0 : 0 < d)
    (hd7 : d < 7) (h : y ^ d * w * (y ^ d)⁻¹ = w) : y * w * y⁻¹ = w := by
  have hy7 : y ^ 7 = 1 := by rw [← hy, pow_orderOf_eq_one]
  have hpow : ∀ n : ℕ, y ^ (n % 7) = y ^ n := fun n => by
    rw [← hy, pow_mod_orderOf]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (d * m) % 7 = 1 := by
    interval_cases d
    · exact ⟨1, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨6, by norm_num⟩
  have hym : y = (y ^ d) ^ m := by
    rw [← pow_mul, ← hpow (d * m), hm, pow_one]
  rw [hym]
  exact conj_pow_eq h m

theorem orbit_of_ne_one {y : X} (hy : orderOf y = 7) {S : Subgroup X} (hS8 : Nat.card S = 8)
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1)
    {w : X} (hw : w ∈ S) (hw1 : w ≠ 1) {s : X} (hs : s ∈ S) :
    s = 1 ∨ ∃ k : ℕ, k < 7 ∧ s = y ^ k * w * (y ^ k)⁻¹ := by
  classical
  set σ : ℕ → X := fun k => y ^ k * w * (y ^ k)⁻¹ with hσdef
  have hσS : ∀ k, σ k ∈ S := fun k => conj_pow_mem hyS hw k
  have hlt : ∀ k l : ℕ, k < l → l < 7 → σ k ≠ σ l := by
    intro k l hkl hl h
    obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
    have hd0 : 0 < d := by omega
    have hd7 : d < 7 := by omega
    have hσl : σ (k + d) = y ^ k * (y ^ d * w * (y ^ d)⁻¹) * (y ^ k)⁻¹ := by
      simp only [hσdef, pow_add]
      group
    have h' : y ^ k * w * (y ^ k)⁻¹ = y ^ k * (y ^ d * w * (y ^ d)⁻¹) * (y ^ k)⁻¹ := by
      rw [← hσl]
      exact h
    have hfix : y ^ d * w * (y ^ d)⁻¹ = w := by
      have e1 : (y ^ k)⁻¹ * (y ^ k * w * (y ^ k)⁻¹) * y ^ k = w := by group
      have e2 : (y ^ k)⁻¹ * (y ^ k * (y ^ d * w * (y ^ d)⁻¹) * (y ^ k)⁻¹) * y ^ k =
          y ^ d * w * (y ^ d)⁻¹ := by group
      calc y ^ d * w * (y ^ d)⁻¹ = (y ^ k)⁻¹ * (y ^ k * (y ^ d * w * (y ^ d)⁻¹) * (y ^ k)⁻¹)
            * y ^ k := e2.symm
        _ = (y ^ k)⁻¹ * (y ^ k * w * (y ^ k)⁻¹) * y ^ k := by rw [h']
        _ = w := e1
    exact hw1 (hfpf w hw (conj_fix_of_pow_fix hy hd0 hd7 hfix))
  have hinjOn : Set.InjOn σ (Finset.range 7 : Set ℕ) := by
    intro k hk l hl hkl
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt k l h hl hkl
    · exact hlt l k h hk hkl.symm
  set T : Finset X := (Finset.range 7).image σ with hT
  have hTcard : T.card = 7 := by
    rw [hT, Finset.card_image_of_injOn hinjOn, Finset.card_range]
  have h1T : (1 : X) ∉ T := by
    intro h1
    rw [hT, Finset.mem_image] at h1
    obtain ⟨k, -, hk⟩ := h1
    have hk' : y ^ k * w * (y ^ k)⁻¹ = 1 := hk
    apply hw1
    calc w = (y ^ k)⁻¹ * (y ^ k * w * (y ^ k)⁻¹) * y ^ k := by group
      _ = 1 := by rw [hk']; group
  have hU : (insert (1 : X) (T : Set X)) ⊆ (S : Set X) := by
    intro x hx
    rcases hx with rfl | hx
    · exact S.one_mem
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact hσS k
  have hT8 : (insert (1 : X) (T : Set X)).ncard = 8 := by
    rw [Set.ncard_insert_of_notMem (by simpa using h1T), Set.ncard_coe_finset, hTcard]
  have hSn : (S : Set X).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hS8
  have hSfin : (S : Set X).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have heq : insert (1 : X) (T : Set X) = (S : Set X) :=
    Set.eq_of_subset_of_ncard_le hU (by omega) hSfin
  have hsU : s ∈ insert (1 : X) (T : Set X) := by
    rw [heq]
    exact hs
  rcases hsU with rfl | hsT
  · exact Or.inl rfl
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hsT)
    exact Or.inr ⟨k, Finset.mem_range.1 hk, rfl⟩

end CFSG.GF2Type.Smith1979.Case2.U43Grp
