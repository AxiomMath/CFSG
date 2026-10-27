module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open Polynomial
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_smul_one_of_commute (M : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ b : SL(2, F), M * (b : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F) * M) :
    M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hu := h ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hl := h ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have e1 := congrFun (congrFun hu 0) 0
  have e2 := congrFun (congrFun hu 0) 1
  have e3 := congrFun (congrFun hl 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact e3
  · exact e1
  · linear_combination -e2

theorem exists_pow_succ_eq [Finite F] {m : ℕ} (hF : Nat.card F = m ^ 2) (hm : 2 ≤ m) {l : F}
    (hl0 : l ≠ 0) (hl : l ^ m = l) : ∃ c : F, c ^ (m + 1) = l := by
  classical
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf γ = m ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hF]
  have hfin : IsOfFinOrder γ := isOfFinOrder_of_finite γ
  obtain ⟨k, hk⟩ := hfin.mem_powers_iff_mem_zpowers.mpr (hγ (Units.mk0 l hl0))
  have hk' : γ ^ k = Units.mk0 l hl0 := hk
  have hl1 : (Units.mk0 l hl0) ^ (m - 1) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have h1 : l ^ (m - 1) * l = 1 * l := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hl, one_mul]
    exact mul_right_cancel₀ hl0 h1
  have hdvd : orderOf γ ∣ k * (m - 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk', hl1]
  have hm2 : m ^ 2 - 1 = (m + 1) * (m - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hord, hm2] at hdvd
  obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < m - 1) hdvd
  refine ⟨((γ ^ j : Fˣ) : F), ?_⟩
  have h2 : (γ ^ j) ^ (m + 1) = Units.mk0 l hl0 := by rw [← pow_mul, mul_comm, ← hj, hk']
  have h3 := congrArg Units.val h2
  simpa using h3

theorem exists_det_smul_add_ne_zero [Finite F] {m : ℕ} (hF : Nat.card F = m ^ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) F) :
    ∃ α : F, (α • (1 : Matrix (Fin 2) (Fin 2) F) + α ^ m • A).det ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set P : F[X] := X ^ 2 + C A.trace * X ^ (m + 1) + C A.det * X ^ (2 * m) with hP
  have hcoeff : P.coeff 2 = 1 := by
    have h1 : ¬ (2 = m + 1) := by omega
    have h2 : ¬ (2 = 2 * m) := by omega
    simp [hP, coeff_X_pow, h1, h2]
  have hP0 : P ≠ 0 := fun h => by simp [h] at hcoeff
  have hdeg : P.natDegree ≤ 2 * m := by
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_X_pow_le 2).trans (by omega)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · exact natDegree_C_mul_X_pow_le _ _
  have hlt : P.natDegree < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    nlinarith
  obtain ⟨α, hα⟩ := exists_eval_ne_zero_of_natDegree_lt_card P hP0 (by
    rw [Cardinal.mk_fintype]
    exact_mod_cast hlt)
  refine ⟨α, ?_⟩
  have hev : (α • (1 : Matrix (Fin 2) (Fin 2) F) + α ^ m • A).det = P.eval α := by
    rw [Matrix.det_fin_two, hP]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [hev]
  exact hα

theorem exists_ringHom_range {p e : ℕ} [Fact p.Prime] (he : 0 < e) :
    ∃ ι : GaloisField p e →+* GaloisField p (2 * e),
      ∀ x : GaloisField p (2 * e), x ^ (p ^ e) = x ↔ x ∈ ι.range := by
  classical
  have h2e : 2 * e ≠ 0 := by omega
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  have : Fintype (GaloisField p (2 * e)) := Fintype.ofFinite _
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
    (K := GaloisField p e) (L := GaloisField p (2 * e)) (by
      rw [GaloisField.finrank p he.ne', GaloisField.finrank p h2e]
      exact Dvd.intro_left 2 rfl)
  have hcardK : Fintype.card (GaloisField p e) = p ^ e := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p e he.ne']
  have hmem : ∀ y : GaloisField p e, (ι y) ^ (p ^ e) = ι y := by
    intro y
    rw [← map_pow, ← hcardK, FiniteField.pow_card]
  refine ⟨ι.toRingHom, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have hp1 : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
    have hQ0 := FiniteField.X_pow_card_sub_X_ne_zero (GaloisField p (2 * e)) hp1
    by_contra hxT
    have hxT' : x ∉ Finset.univ.image ι := by
      intro h
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp h
      exact hxT ⟨y, rfl⟩
    have hS : (insert x (Finset.univ.image ι)).val ⊆
        (X ^ (p ^ e) - X : (GaloisField p (2 * e))[X]).roots := by
      intro y hy
      rw [Polynomial.mem_roots hQ0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
        exact hmem z
    have h1 := Polynomial.card_le_degree_of_subset_roots hS
    rw [Finset.card_insert_of_notMem hxT', Finset.card_image_of_injective _
      (show Function.Injective ι from ι.toRingHom.injective),
      Finset.card_univ, hcardK, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1] at h1
    omega
  · rintro ⟨y, rfl⟩
    exact hmem y

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
