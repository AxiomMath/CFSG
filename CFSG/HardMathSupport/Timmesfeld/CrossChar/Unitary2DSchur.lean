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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_eigen_of_pow_three {B : Module.End K V} (hB3 : ∀ v, B (B (B v)) = v) {w : K}
    (hw : 1 + w + w ^ 2 = 0) (hw3 : w ^ 3 = 1) (W : Submodule K V) (hBW : ∀ v ∈ W, B v ∈ W)
    {y : V} (hyW : y ∈ W) (hy0 : y ≠ 0) :
    ∃ u ∈ W, u ≠ 0 ∧ ∃ μ : K, μ ≠ 0 ∧ B u = μ • u := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hw3
  set y2 : V := B (B y) + B y + y with hy2
  by_cases h2 : y2 ≠ 0
  · refine ⟨y2, ?_, h2, 1, one_ne_zero, ?_⟩
    · exact W.add_mem (W.add_mem (hBW _ (hBW _ hyW)) (hBW _ hyW)) hyW
    · rw [one_smul, hy2, map_add, map_add, hB3]
      abel
  push Not at h2
  set y1 : V := B y - w ^ 2 • y with hy1
  by_cases h1 : y1 ≠ 0
  · refine ⟨y1, W.sub_mem (hBW _ hyW) (W.smul_mem _ hyW), h1, w, hw0, ?_⟩
    have e : B y1 - w • y1 = y2 := by
      have hw' : w ^ 2 + w = -1 := by linear_combination hw
      have h3 : w * w ^ 2 = 1 := by rw [← pow_succ', hw3]
      rw [hy1, hy2, map_sub, map_smul, smul_sub, smul_smul, h3, one_smul]
      calc B (B y) - w ^ 2 • B y - (w • B y - y) = B (B y) - (w ^ 2 + w) • B y + y := by
            rw [add_smul]; abel
        _ = B (B y) + B y + y := by rw [hw', neg_one_smul, sub_neg_eq_add]
    rw [h2] at e
    exact sub_eq_zero.1 e
  push Not at h1
  refine ⟨y, hyW, hy0, w ^ 2, pow_ne_zero 2 hw0, ?_⟩
  exact sub_eq_zero.1 h1

theorem heis_scalar [FiniteDimensional K V] {A B M : Module.End K V} (hA : Function.Injective A)
    {w : K} (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1) (hAB : ∀ v, A (B v) = w • B (A v))
    (hB3 : ∀ v, B (B (B v)) = v) (hMA : ∀ v, M (A v) = A (M v)) (hMB : ∀ v, M (B v) = B (M v))
    (W : Submodule K V) (hAW : ∀ v ∈ W, A v ∈ W) (hBW : ∀ v ∈ W, B v ∈ W)
    (hMW : ∀ v ∈ W, M v ∈ W) (hdim : finrank K W ≤ 3) :
    ∃ c : K, ∀ v ∈ W, M v = c • v := by
  classical
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hw3
  have hw : 1 + w + w ^ 2 = 0 := by
    have h1 : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw3
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hw1
    · exact h
  by_cases hW : W = ⊥
  · refine ⟨0, fun v hv => ?_⟩
    rw [hW, Submodule.mem_bot] at hv
    rw [hv, map_zero, smul_zero]
  obtain ⟨y, hyW, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨u, huW, hu0, μ, hμ0, hBu⟩ := exists_eigen_of_pow_three hB3 hw hw3 W hBW hyW hy0
  have hBA : ∀ v, B (A v) = w⁻¹ • A (B v) := fun v => by
    rw [hAB v, smul_smul, inv_mul_cancel₀ hw0, one_smul]
  set e : Fin 3 → V := ![u, A u, A (A u)] with he
  set ν : Fin 3 → K := ![μ, w⁻¹ * μ, w⁻¹ * (w⁻¹ * μ)] with hν
  have hBe : ∀ i, B (e i) = ν i • e i := by
    intro i
    fin_cases i
    · simpa [he, hν] using hBu
    · simp only [he, hν]
      simp [hBA, hBu, smul_smul]
    · simp only [he, hν]
      simp [hBA, hBu, smul_smul]
  have he0 : ∀ i, e i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [he] using hu0
    · simp only [he]
      simpa using fun h0 => hu0 (hA (by rw [h0, map_zero]))
    · simp only [he]
      simpa using fun h0 => hu0 (hA (hA (by rw [h0, map_zero, map_zero])))
  have hwi1 : w⁻¹ ≠ 1 := fun h1 => hw1 (by rw [← inv_inv w, h1, inv_one])
  have hwi2 : w⁻¹ * w⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have : w⁻¹ * w⁻¹ * w ^ 3 = w := by
      field_simp
    rw [h1, hw3, one_mul] at this
    exact this.symm
  have hνinj : Function.Injective ν := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [hν] at hij ⊢ <;>
      first
      | rfl
      | (exfalso
         first
         | exact hwi1 (mul_right_cancel₀ hμ0 (by simpa using hij.symm))
         | exact hwi1 (mul_right_cancel₀ hμ0 (by simpa using hij))
         | exact hwi2 (mul_right_cancel₀ hμ0 (by simpa [mul_assoc] using hij.symm))
         | exact hwi2 (mul_right_cancel₀ hμ0 (by simpa [mul_assoc] using hij))
         | exact hwi1 (mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hw0) hμ0)
             (by simpa [mul_assoc] using hij.symm))
         | exact hwi1 (mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hw0) hμ0)
             (by simpa [mul_assoc] using hij)))
  have hli : LinearIndependent K e :=
    Module.End.eigenvectors_linearIndependent' B ν hνinj e fun i =>
      ⟨Module.End.mem_eigenspace_iff.2 (hBe i), he0 i⟩
  have heW : ∀ i, e i ∈ W := by
    intro i
    fin_cases i
    · simpa [he] using huW
    · simpa [he] using hAW _ huW
    · simpa [he] using hAW _ (hAW _ huW)
  have hspan : Submodule.span K (Set.range e) = W := by
    refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact heW i
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact hdim
  obtain ⟨a, ha⟩ : ∃ a : K, M u = a • u := by
    have hMu : M u ∈ Submodule.span K (Set.range e) := by
      rw [hspan]
      exact hMW u huW
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hMu
    have hBMu : B (M u) = μ • M u := by rw [← hMB, hBu, map_smul]
    have h0 : ∑ i, (d i * (ν i - μ)) • e i = 0 := by
      have : ∑ i, (d i * (ν i - μ)) • e i = B (M u) - μ • M u := by
        rw [← hd, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hBe i, smul_smul, smul_smul, ← sub_smul, mul_sub, mul_comm (d i) μ,
          mul_comm (d i) (ν i)]
      rw [this, hBMu, sub_self]
    have hz := (Fintype.linearIndependent_iff.1 hli) _ h0
    have hd1 : d 1 = 0 := by
      have := hz 1
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) (fun h' => hνinj.ne (show (1 : Fin 3) ≠ 0 by decide) h')
    have hd2 : d 2 = 0 := by
      have := hz 2
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) (fun h' => hνinj.ne (show (2 : Fin 3) ≠ 0 by decide) h')
    refine ⟨d 0, ?_⟩
    rw [← hd, Fin.sum_univ_three, hd1, hd2, zero_smul, zero_smul, add_zero, add_zero]
    rfl
  have hMe : ∀ i, M (e i) = a • e i := by
    intro i
    fin_cases i
    · simpa [he] using ha
    · simp only [he]
      simp [hMA, ha]
    · simp only [he]
      simp [hMA, ha]
  refine ⟨a, fun v hv => ?_⟩
  rw [← hspan] at hv
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hMe i, smul_comm]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
