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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open Matrix

theorem exists_prime_order_inverted {G Q : Type*} [Group G] [Group Q] (q : G →* Q)
    (hker : ∀ z, q z = 1 → z ∈ Subgroup.center G) (Gh : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) {x n : G} (hx : x ∈ Gh) (hn : n ∈ Gh) (hxp : q x ^ p = 1)
    (hinv : q (n * x * n⁻¹) = (q x)⁻¹) :
    ∃ y ∈ Gh, y ^ p = 1 ∧ q y = q x := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
  have hgG : n * x * n⁻¹ ∈ Gh := Gh.mul_mem (Gh.mul_mem hn hx) (Gh.inv_mem hn)
  set z := x * (n * x * n⁻¹) with hz
  have hzG : z ∈ Gh := Gh.mul_mem hx hgG
  have hcG : x ^ p ∈ Gh := Gh.pow_mem hx p
  have hqz : q z = 1 := by rw [hz, map_mul, hinv, mul_inv_cancel]
  have hqc : q (x ^ p) = 1 := by rw [map_pow]; exact hxp
  have hzC : z ∈ Subgroup.center G := hker z hqz
  have hcC : x ^ p ∈ Subgroup.center G := hker _ hqc
  have hgx : n * x * n⁻¹ = x⁻¹ * z := by rw [hz]; group
  have h1 : (n * x * n⁻¹) ^ p = x ^ p := by
    rw [conj_pow, Subgroup.mem_center_iff.1 hcC n, mul_inv_cancel_right]
  have hcomm : Commute x⁻¹ z := Subgroup.mem_center_iff.1 hzC x⁻¹
  have h2 : (n * x * n⁻¹) ^ p = (x ^ p)⁻¹ * z ^ p := by
    rw [hgx, hcomm.mul_pow, inv_pow]
  have h3 : x ^ p * x ^ p = z ^ p := by
    have h5 : x ^ p = (x ^ p)⁻¹ * z ^ p := h1.symm.trans h2
    calc x ^ p * x ^ p = x ^ p * ((x ^ p)⁻¹ * z ^ p) := by rw [← h5]
      _ = z ^ p := by group
  set w := z ^ (m + 1) * (x ^ p)⁻¹ with hw
  have hwG : w ∈ Gh := Gh.mul_mem (Gh.pow_mem hzG _) (Gh.inv_mem hcG)
  have hwC : w ∈ Subgroup.center G :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hzC _) (Subgroup.inv_mem _ hcC)
  have hqw : q w = 1 := by rw [hw, map_mul, map_pow, hqz, one_pow, map_inv, hqc, inv_one, one_mul]
  have h4 : w ^ p = x ^ p := by
    have hcm : Commute (z ^ (m + 1)) (x ^ p)⁻¹ :=
      Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hcC) (z ^ (m + 1))
    rw [hw, hcm.mul_pow, ← pow_mul, mul_comm (m + 1) p, pow_mul, ← h3, inv_pow, ← pow_two, ← pow_mul, hm]
    group
  refine ⟨x * w⁻¹, Gh.mul_mem hx (Gh.inv_mem hwG), ?_, ?_⟩
  · have hc2 : Commute x w⁻¹ := (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hwC) x)
    rw [hc2.mul_pow, inv_pow, h4, mul_inv_cancel]
  · rw [map_mul, map_inv, hqw, inv_one, mul_one]

theorem exists_involution_inverting {F : Type*} [Field F] [CharP F 2]
    (h : SpecialLinearGroup (Fin 2) F) :
    ∃ n : SpecialLinearGroup (Fin 2) F, n * n = 1 ∧ n * h * n⁻¹ = h⁻¹ := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg : ∀ x : F, -x = x := fun x => by
    have : x + x = 0 := by rw [← two_mul, h2, zero_mul]
    exact neg_eq_of_add_eq_zero_right this
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d + b * c = 1 := by
    have := h.2
    rw [hM, Matrix.det_fin_two_of] at this
    linear_combination this + (b * c) * h2
  have hinv : ((h⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![d, b; c, a] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hM]
    simp [hneg]
  have key : ∀ u : SpecialLinearGroup (Fin 2) F, u * u = 1 →
      (u : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, d] * (u : Matrix (Fin 2) (Fin 2) F) =
        !![d, b; c, a] → ∃ n : SpecialLinearGroup (Fin 2) F, n * n = 1 ∧ n * h * n⁻¹ = h⁻¹ := by
    intro u hu hq
    refine ⟨u, hu, ?_⟩
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    rw [hui]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, hM]
    exact hq
  have hss : ∀ s : F, s + s = 0 := fun s => by rw [← two_mul, h2, zero_mul]
  have mk : ∀ (u : Matrix (Fin 2) (Fin 2) F), u.det = 1 → u * u = 1 →
      (u * !![a, b; c, d] * u = !![d, b; c, a]) →
      ∃ n : SpecialLinearGroup (Fin 2) F, n * n = 1 ∧ n * h * n⁻¹ = h⁻¹ := by
    intro u hdu huu hq
    let U : SpecialLinearGroup (Fin 2) F := ⟨u, hdu⟩
    refine key U ?_ hq
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact huu
  by_cases hc0 : c = 0
  · by_cases hb0 : b = 0
    · refine mk !![0, 1; 1, 0] (by rw [Matrix.det_fin_two_of]; simp [hneg]) ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb0, hc0]
    · obtain ⟨s, hs⟩ : ∃ s : F, s * b = a + d := ⟨(a + d) / b, div_mul_cancel₀ _ hb0⟩
      refine mk !![1, 0; s, 1] (by rw [Matrix.det_fin_two_of]; simp) ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hss]
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc0]
        · linear_combination hs + a * h2
        · linear_combination s * hs + (s * a + s * d) * h2
        · linear_combination hs + d * h2
  · obtain ⟨s, hs⟩ : ∃ s : F, s * c = a + d := ⟨(a + d) / c, div_mul_cancel₀ _ hc0⟩
    refine mk !![1, s; 0, 1] (by rw [Matrix.det_fin_two_of]; simp) ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hss]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hs + a * h2
      · linear_combination s * hs + (s * a + s * d) * h2
      · linear_combination hs + d * h2

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
