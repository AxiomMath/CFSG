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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.K32A

open Matrix

variable {K : Type} [Field K]

abbrev sc (u : Kˣ) : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) u

theorem sc_mem_center (u : Kˣ) : (sc u : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

theorem mul_sc_comm (u : Kˣ) (g : GL (Fin 3) K) : g * sc u = sc u * g :=
  Subgroup.mem_center_iff.1 (sc_mem_center u) g

theorem sc_one : (sc 1 : GL (Fin 3) K) = 1 := map_one _

theorem sc_mul (u v : Kˣ) : (sc (u * v) : GL (Fin 3) K) = sc u * sc v := map_mul _ _ _

theorem sc_pow (u : Kˣ) (n : ℕ) : (sc (u ^ n) : GL (Fin 3) K) = sc u ^ n := map_pow _ _ _

theorem commute_sc (u : Kˣ) (g : GL (Fin 3) K) : Commute (sc u) g := (mul_sc_comm u g).symm

theorem trace_conj (X W : GL (Fin 3) K) :
    ((X * W * X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (W : Matrix (Fin 3) (Fin 3) K).trace := by
  calc ((X * W * X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace
      = (((X * W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace := by rw [Units.val_mul]
    _ = (((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((X * W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace := Matrix.trace_mul_comm _ _
    _ = ((X⁻¹ * (X * W) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
        simp only [Units.val_mul]
    _ = (W : Matrix (Fin 3) (Fin 3) K).trace := by rw [inv_mul_cancel_left]

theorem trace_sc_mul (u : Kˣ) (W : GL (Fin 3) K) :
    ((sc u * W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (u : K) * (W : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

theorem trace_eq_zero_of_conj (X W : GL (Fin 3) K) (u : Kˣ) (hu : u ≠ 1)
    (h : X * W * X⁻¹ = sc u * W) : (W : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  have h1 := trace_conj X W
  rw [h, trace_sc_mul] at h1
  have h2 : ((u : K) - 1) * (W : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (Units.ext (sub_eq_zero.1 h3)) hu
  · exact h3

section Heis

variable {A B : GL (Fin 3) K} {ν : Kˣ}

theorem conj_inv_of_heis (hAB : A * B * A⁻¹ = sc ν * B) : B * A * B⁻¹ = (sc ν)⁻¹ * A := by
  have e : A * B = sc ν * B * A := by
    calc A * B = (A * B * A⁻¹) * A := by group
      _ = sc ν * B * A := by rw [hAB]
  calc B * A * B⁻¹ = (sc ν)⁻¹ * (sc ν * B * A) * B⁻¹ := by group
    _ = (sc ν)⁻¹ * (A * B) * B⁻¹ := by rw [e]
    _ = (sc ν)⁻¹ * A := by group

theorem trace_zpow_mul_zpow (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1) (hAB : A * B * A⁻¹ = sc ν * B)
    (m n : ℤ) (h : ¬ ((3 : ℤ) ∣ m ∧ (3 : ℤ) ∣ n)) :
    ((A ^ m * B ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ν = 3 := orderOf_eq_prime hν3 hν1
  have hpow : ∀ k : ℤ, ν ^ k = 1 → (3 : ℤ) ∣ k := fun k hk => by
    have := orderOf_dvd_iff_zpow_eq_one.2 hk
    rwa [hord] at this
  by_cases hm : (3 : ℤ) ∣ m
  · have hn : ¬ (3 : ℤ) ∣ n := fun hn => h ⟨hm, hn⟩
    refine trace_eq_zero_of_conj A (A ^ m * B ^ n) (ν ^ n) (fun h1 => hn (hpow n h1)) ?_
    have e1 : A * B ^ n * A⁻¹ = sc (ν ^ n) * B ^ n := by
      rw [← conj_zpow, hAB, Commute.mul_zpow (commute_sc ν B), ← map_zpow]
    calc A * (A ^ m * B ^ n) * A⁻¹ = A ^ m * (A * B ^ n * A⁻¹) := by group
      _ = A ^ m * (sc (ν ^ n) * B ^ n) := by rw [e1]
      _ = (A ^ m * sc (ν ^ n)) * B ^ n := by rw [mul_assoc]
      _ = sc (ν ^ n) * (A ^ m * B ^ n) := by rw [mul_sc_comm, mul_assoc]
  · refine trace_eq_zero_of_conj B (A ^ m * B ^ n) (ν⁻¹ ^ m) (fun h1 => hm (hpow m ?_)) ?_
    · rwa [_root_.inv_zpow, inv_eq_one] at h1
    have e1 : B * A ^ m * B⁻¹ = sc (ν⁻¹ ^ m) * A ^ m := by
      rw [← conj_zpow, conj_inv_of_heis hAB, Commute.mul_zpow (commute_sc ν A).inv_left,
        ← map_inv, ← map_zpow]
    calc B * (A ^ m * B ^ n) * B⁻¹ = (B * A ^ m * B⁻¹) * B ^ n := by group
      _ = sc (ν⁻¹ ^ m) * (A ^ m * B ^ n) := by rw [e1, mul_assoc]

theorem span_eq_top_of_trace_orth (h3 : (3 : K) ≠ 0) {ι : Type} [Fintype ι]
    (hι : Fintype.card ι = 9) (e : ι → GL (Fin 3) K)
    (htr : ∀ i j, i ≠ j →
      ((e i : Matrix (Fin 3) (Fin 3) K) *
        (((e j)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace = 0) :
    Submodule.span K (Set.range fun i => (e i : Matrix (Fin 3) (Fin 3) K)) = ⊤ := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  refine LinearIndependent.span_eq_top_of_card_eq_finrank ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h := congrArg (fun M => (M * (((e j)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)).trace) hg
    simp only [Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, zero_mul,
      Matrix.trace_zero] at h
    rw [Finset.sum_eq_single j] at h
    · have h1 : ((e j : Matrix (Fin 3) (Fin 3) K) *
          (((e j)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [h1] at h
      simp at h
      exact h.resolve_right h3
    · intro i _ hij
      rw [htr i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · rw [hι, Module.finrank_matrix]
    simp

theorem mem_center_of_commute_span {ι : Type} (e : ι → GL (Fin 3) K)
    (hspan : Submodule.span K (Set.range fun i => (e i : Matrix (Fin 3) (Fin 3) K)) = ⊤)
    (d : GL (Fin 3) K) (hd : ∀ i, d * e i = e i * d) :
    d ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hle : Submodule.span K (Set.range fun i => (e i : Matrix (Fin 3) (Fin 3) K)) ≤
      (Subalgebra.centralizer K ({(d : Matrix (Fin 3) (Fin 3) K)} :
        Set (Matrix (Fin 3) (Fin 3) K))).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    rw [hm, ← Units.val_mul, ← Units.val_mul, hd i]
  have hg : (g : Matrix (Fin 3) (Fin 3) K) ∈
      (Subalgebra.centralizer K ({(d : Matrix (Fin 3) (Fin 3) K)} :
        Set (Matrix (Fin 3) (Fin 3) K))).toSubmodule := hle (by rw [hspan]; trivial)
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hg
  exact Units.ext (hg _ (Set.mem_singleton _)).symm

theorem mem_center_of_commute_heis (h3 : (3 : K) ≠ 0) (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1)
    (hAB : A * B * A⁻¹ = sc ν * B) (d : GL (Fin 3) K) (hdA : d * A = A * d)
    (hdB : d * B = B * d) : d ∈ Subgroup.center (GL (Fin 3) K) := by
  let e : Fin 3 × Fin 3 → GL (Fin 3) K := fun p => A ^ ((p.1 : ℕ) : ℤ) * B ^ ((p.2 : ℕ) : ℤ)
  have htr : ∀ p q : Fin 3 × Fin 3, p ≠ q →
      ((e p : Matrix (Fin 3) (Fin 3) K) *
        (((e q)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace = 0 := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hpq
    rw [← Units.val_mul]
    have hc : e (i, j) * (e (k, l))⁻¹ = A ^ ((k : ℕ) : ℤ) *
        (A ^ (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) * B ^ (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))) *
          (A ^ ((k : ℕ) : ℤ))⁻¹ := by
      simp only [e]
      group
    rw [hc, trace_conj]
    apply trace_zpow_mul_zpow hν3 hν1 hAB
    rintro ⟨h1, h2⟩
    apply hpq
    have := i.isLt
    have := j.isLt
    have := k.isLt
    have := l.isLt
    exact Prod.ext (Fin.ext (show (i : ℕ) = k by omega)) (Fin.ext (show (j : ℕ) = l by omega))
  have hspan := span_eq_top_of_trace_orth h3 (by simp) e htr
  refine mem_center_of_commute_span e hspan d fun p => ?_
  have cA : Commute d A := hdA
  have cB : Commute d B := hdB
  exact ((cA.zpow_right _).mul_right (cB.zpow_right _)).eq

end Heis

section Order3

theorem mem_center_of_eq_smul_one {g : GL (Fin 3) K} {a : K}
    (h : (g : Matrix (Fin 3) (Fin 3) K) = a • (1 : Matrix (Fin 3) (Fin 3) K)) :
    g ∈ Subgroup.center (GL (Fin 3) K) := by
  have ha : a ≠ 0 := by
    rintro rfl
    have := g.mul_inv
    rw [h, zero_smul, zero_mul] at this
    exact zero_ne_one this
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 a ha, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, h, Matrix.smul_one_eq_diagonal]
  rfl

theorem trace_eq_zero_of_cube {U : Matrix (Fin 3) (Fin 3) K}
    (hU3 : U ^ 3 = 1) (hdet : U.det = 1)
    (hns : ∀ a : K, U ≠ a • (1 : Matrix (Fin 3) (Fin 3) K)) : U.trace = 0 := by
  have hcp := Matrix.aeval_self_charpoly U
  have hmon := Matrix.charpoly_monic U
  have hdeg : U.charpoly.natDegree = 3 := by
    simp [Matrix.charpoly_natDegree_eq_dim U]
  have hc3 : U.charpoly.coeff 3 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  have hc2 : U.charpoly.coeff 2 = - U.trace := by
    have := Matrix.trace_eq_neg_charpoly_coeff U
    simp at this
    rw [this]; ring
  have hc0 : U.charpoly.coeff 0 = -1 := by
    have := Matrix.det_eq_sign_charpoly_coeff U
    rw [hdet] at this
    simp at this
    linear_combination this
  rw [Polynomial.aeval_eq_sum_range, hdeg] at hcp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc3, hc2, hc0, pow_zero,
    pow_one, hU3] at hcp
  have h1 : U.charpoly.coeff 1 • U = U.trace • U ^ 2 := by
    rw [← sub_eq_zero, ← hcp]
    module
  have h2 : U.charpoly.coeff 1 • U ^ 2 = U.trace • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (U * ·) h1
    simp only [mul_smul_comm, ← pow_succ', hU3] at this
    simpa [pow_two] using this
  have h3 : U.charpoly.coeff 1 • (1 : Matrix (Fin 3) (Fin 3) K) = U.trace • U := by
    have := congrArg (U * ·) h2
    simp only [mul_smul_comm, ← pow_succ', hU3, mul_one] at this
    simpa using this
  by_contra ht
  apply hns (U.charpoly.coeff 1 / U.trace)
  calc U = U.trace⁻¹ • (U.trace • U) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = U.trace⁻¹ • (U.charpoly.coeff 1 • (1 : Matrix (Fin 3) (Fin 3) K)) := by rw [h3]
    _ = _ := by rw [smul_smul, div_eq_inv_mul]

theorem trace_eq_zero_of_cube_of_not_center {g : GL (Fin 3) K} (hg3 : g ^ 3 = 1)
    (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hns : g ∉ Subgroup.center (GL (Fin 3) K)) : (g : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  refine trace_eq_zero_of_cube ?_ hdet fun a ha => hns (mem_center_of_eq_smul_one ha)
  rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]

end Order3

section Diag

theorem three_ne_zero_of_cube_root {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : (3 : K) ≠ 0 := by
  intro h3
  apply hτ1
  have h : (τ - 1) ^ 3 = 0 := by linear_combination hτ - τ * (τ - 1) * h3
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)

theorem cube_root_ne_zero {τ : K} (hτ : τ ^ 3 = 1) : τ ≠ 0 := by
  rintro rfl
  simp at hτ

theorem cube_root_sq_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ ^ 2 ≠ 1 := by
  intro h
  apply hτ1
  have e : τ ^ 3 = τ * τ ^ 2 := by ring
  rw [e, h] at hτ
  simpa using hτ

theorem cube_root_ne_sq {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ ≠ τ ^ 2 := by
  intro h
  have h0 := cube_root_ne_zero hτ
  apply hτ1
  have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
  exact mul_left_cancel₀ h0 this

theorem det_sub_smul_one_eq_zero (h3 : (3 : K) ≠ 0) {U : Matrix (Fin 3) (Fin 3) K}
    (hU3 : U ^ 3 = 1) (ht1 : U.trace = 0) (ht2 : (U ^ 2).trace = 0) {r : K} (hr : r ^ 3 = 1) :
    (U - r • (1 : Matrix (Fin 3) (Fin 3) K)).det = 0 := by
  by_contra hdet
  have hu : IsUnit (U - r • (1 : Matrix (Fin 3) (Fin 3) K)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hprod : (U - r • (1 : Matrix (Fin 3) (Fin 3) K)) *
      (U ^ 2 + r • U + (r ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
    have e : (U - r • (1 : Matrix (Fin 3) (Fin 3) K)) *
        (U ^ 2 + r • U + (r ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)) =
          U * U ^ 2 - (r ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, ← sq]
      module
    rw [e, ← pow_succ', hU3, hr, one_smul, sub_self]
  have h2 := hu.mul_right_eq_zero.1 hprod
  have h4 := congrArg Matrix.trace h2
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, ht1, ht2, smul_eq_mul,
    Matrix.trace_zero] at h4
  have h5 : r ^ 2 * 3 = 0 := by simpa using h4
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact (mul_ne_zero (pow_ne_zero 2 hr0) h3) h5

theorem exists_diagonalizing {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K}
    (hg3 : g ^ 3 = 1) (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hg : g ∉ Subgroup.center (GL (Fin 3) K)) :
    ∃ P : GL (Fin 3) K, ∀ h : GL (Fin 3) K, h * g = g * h →
      ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal fun i => ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i := by
  have h3 := three_ne_zero_of_cube_root hτ hτ1
  have hτ2 := cube_root_sq_ne_one hτ hτ1
  have hττ2 := cube_root_ne_sq hτ hτ1
  have hU3 : (g : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have ht1 : (g : Matrix (Fin 3) (Fin 3) K).trace = 0 :=
    trace_eq_zero_of_cube_of_not_center hg3 hdet hg
  have ht2 : ((g : Matrix (Fin 3) (Fin 3) K) ^ 2).trace = 0 := by
    have hg2 : g ^ 2 ∉ Subgroup.center (GL (Fin 3) K) := by
      intro h2
      apply hg
      have : (g ^ 2)⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hg3)
      rw [← this]
      exact inv_mem h2
    have := trace_eq_zero_of_cube_of_not_center (g := g ^ 2)
      (by rw [← pow_mul, mul_comm, pow_mul, hg3, one_pow])
      (by rw [Units.val_pow_eq_pow_val, Matrix.det_pow, hdet, one_pow]) hg2
    rwa [Units.val_pow_eq_pow_val] at this
  have hr3 : ∀ i : Fin 3, (τ ^ (i : ℕ)) ^ 3 = 1 := fun i => by
    rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  have hex : ∀ i : Fin 3, ∃ v : Fin 3 → K, v ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (τ ^ (i : ℕ)) • v := fun i => by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2
      (det_sub_smul_one_eq_zero h3 hU3 ht1 ht2 (hr3 i))
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  choose v hv0 hv using hex
  have hinj : Function.Injective fun i : Fin 3 => τ ^ (i : ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hτ1, hτ1.symm, hτ2, hτ2.symm, hττ2, hττ2.symm] at hij ⊢
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K))
      (fun i : Fin 3 => τ ^ (i : ℕ)) hinj v fun i => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨by simpa [Matrix.toLin'_apply] using hv i, hv0 i⟩
  let P0 : Matrix (Fin 3) (Fin 3) K := Matrix.of fun r i => v i r
  have hP0 : IsUnit P0 := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  let P : GL (Fin 3) K := hP0.unit
  have hPval : (P : Matrix (Fin 3) (Fin 3) K) = P0 := rfl
  have hUP : (g : Matrix (Fin 3) (Fin 3) K) * P0 =
      P0 * Matrix.diagonal (fun i : Fin 3 => τ ^ (i : ℕ)) := by
    ext a i
    rw [Matrix.mul_diagonal]
    have := congrFun (hv i) a
    simpa [P0, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have hD : ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i : Fin 3 => τ ^ (i : ℕ)) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hPval, hUP, ← Matrix.mul_assoc,
      ← hPval, Units.inv_mul, Matrix.one_mul]
  refine ⟨P, fun h hgh => ?_⟩
  have hcomm : (P⁻¹ * h * P) * (P⁻¹ * g * P) = (P⁻¹ * g * P) * (P⁻¹ * h * P) := by
    calc (P⁻¹ * h * P) * (P⁻¹ * g * P) = P⁻¹ * (h * g) * P := by group
      _ = P⁻¹ * (g * h) * P := by rw [hgh]
      _ = (P⁻¹ * g * P) * (P⁻¹ * h * P) := by group
  have hcomm' := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hcomm
  simp only [Units.val_mul] at hcomm'
  have hcomm'' : ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal (fun i : Fin 3 => τ ^ (i : ℕ)) =
      Matrix.diagonal (fun i : Fin 3 => τ ^ (i : ℕ)) *
        ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hD]
    simpa only [Units.val_mul] using hcomm'
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · have e := congrFun (congrFun hcomm'' i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    have hne : τ ^ (i : ℕ) ≠ τ ^ (j : ℕ) := fun h => hij (hinj h)
    have : ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j *
        (τ ^ (j : ℕ) - τ ^ (i : ℕ)) = 0 := by
      linear_combination e
    rcases mul_eq_zero.1 this with h0 | h0
    · simp [h0, Matrix.diagonal_apply_ne _ hij]
    · exact absurd (sub_eq_zero.1 h0).symm hne

theorem coe_sc_mul (u : Kˣ) (X : GL (Fin 3) K) :
    ((sc u * X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (u : K) • (X : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem sc_conj (P : GL (Fin 3) K) (u : Kˣ) : P * sc u * P⁻¹ = sc u := by
  rw [mul_sc_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_ratio {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K}
    (hg3 : g ^ 3 = 1) (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hg : g ∉ Subgroup.center (GL (Fin 3) K)) :
    ∃ f : GL (Fin 3) K → K,
      (∀ h : GL (Fin 3) K, h * g = g * h → h ^ 3 = 1 →
        (h : Matrix (Fin 3) (Fin 3) K).det = 1 → f h ^ 3 = 1) ∧
      ∀ h h' : GL (Fin 3) K, h * g = g * h → h ^ 3 = 1 →
        (h : Matrix (Fin 3) (Fin 3) K).det = 1 → h' * g = g * h' → h' ^ 3 = 1 →
        (h' : Matrix (Fin 3) (Fin 3) K).det = 1 → f h = f h' →
        h⁻¹ * h' ∈ Subgroup.center (GL (Fin 3) K) := by
  obtain ⟨P, hP⟩ := exists_diagonalizing hτ hτ1 hg3 hdet hg
  obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin 3) K → Fin 3 → K, ∀ h i,
      δ h i = ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i :=
    ⟨fun h i => _, fun _ _ => rfl⟩
  have hdiag : ∀ h : GL (Fin 3) K, h * g = g * h →
      ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (δ h) :=
    fun h hgh => by
      rw [hP h hgh]
      congr 1
      funext i
      rw [hδ]
  have key : ∀ h : GL (Fin 3) K, h * g = g * h → h ^ 3 = 1 →
      (h : Matrix (Fin 3) (Fin 3) K).det = 1 → (∀ i, δ h i ^ 3 = 1) ∧ δ h 0 * δ h 1 * δ h 2 = 1 := by
    intro h hgh h3 hd
    refine ⟨fun i => ?_, ?_⟩
    · have e : (P⁻¹ * h * P) ^ 3 = 1 := by
        calc (P⁻¹ * h * P) ^ 3 = P⁻¹ * h ^ 3 * P := by
              simp only [pow_succ, pow_zero, one_mul]
              group
          _ = 1 := by rw [h3]; group
      have e2 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) e
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at e2
      rw [hdiag h hgh, Matrix.diagonal_pow] at e2
      have := congrFun (congrFun e2 i) i
      simpa using this
    · have e : ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj', hd]
      rw [hdiag h hgh, Matrix.det_diagonal, Fin.prod_univ_three] at e
      exact e
  refine ⟨fun h => δ h 0 / δ h 1, fun h hgh h3 hd => ?_, ?_⟩
  · obtain ⟨hk1, -⟩ := key h hgh h3 hd
    simp only [div_pow, hk1 0, hk1 1, div_one]
  · intro h h' hgh h3 hd hgh' h3' hd' hf
    obtain ⟨hk1, hk2⟩ := key h hgh h3 hd
    obtain ⟨hk1', hk2'⟩ := key h' hgh' h3' hd'
    have hne : ∀ x : K, x ^ 3 = 1 → x ≠ 0 := fun x hx => by
      rintro rfl
      simp at hx
    have ha0 := hne _ (hk1 0)
    have ha1 := hne _ (hk1 1)
    have ha2 := hne _ (hk1 2)
    have hb1 := hne _ (hk1' 1)
    set c : K := δ h' 0 / δ h 0 with hc
    have hc0 : c ≠ 0 := div_ne_zero (hne _ (hk1' 0)) ha0
    have hc3 : c ^ 3 = 1 := by rw [hc, div_pow, hk1' 0, hk1 0, div_one]
    have e0 : δ h' 0 = c * δ h 0 := by rw [hc]; field_simp
    have e1 : δ h' 1 = c * δ h 1 := by
      have := (div_eq_div_iff ha1 hb1).1 hf
      rw [hc]
      field_simp
      linear_combination this
    have e2 : δ h' 2 = c * δ h 2 := by
      have h1 : δ h 0 * δ h 1 * (c ^ 2 * δ h' 2 - δ h 2) = 0 := by
        rw [e0, e1] at hk2'
        linear_combination hk2' - hk2
      have h2 : c ^ 2 * δ h' 2 = δ h 2 := by
        have := (mul_eq_zero.1 h1).resolve_left (mul_ne_zero ha0 ha1)
        exact sub_eq_zero.1 this
      calc δ h' 2 = c ^ 3 * δ h' 2 := by rw [hc3, one_mul]
        _ = c * (c ^ 2 * δ h' 2) := by ring
        _ = c * δ h 2 := by rw [h2]
    have hmat : ((P⁻¹ * h' * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((sc (Units.mk0 c hc0) * (P⁻¹ * h * P) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hdiag h' hgh', coe_sc_mul, hdiag h hgh, Units.val_mk0, ← Matrix.diagonal_smul]
      congr 1
      funext i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
    have hP' : P⁻¹ * h' * P = sc (Units.mk0 c hc0) * (P⁻¹ * h * P) := Units.ext hmat
    have hh' : h' = sc (Units.mk0 c hc0) * h := by
      calc h' = P * (P⁻¹ * h' * P) * P⁻¹ := by group
        _ = P * (sc (Units.mk0 c hc0) * (P⁻¹ * h * P)) * P⁻¹ := by rw [hP']
        _ = (P * sc (Units.mk0 c hc0) * P⁻¹) * h := by group
        _ = sc (Units.mk0 c hc0) * h := by rw [sc_conj]
    rw [hh', ← mul_sc_comm, inv_mul_cancel_left]
    exact sc_mem_center _

end Diag

section Scalars

theorem sc_injective : Function.Injective (sc : Kˣ → GL (Fin 3) K) := by
  intro u v h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using Units.ext this

theorem det_sc (u : Kˣ) : Matrix.GeneralLinearGroup.det (sc u : GL (Fin 3) K) = u ^ 3 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.det_diagonal]
  simp

theorem exists_sc_of_center {s : GL (Fin 3) K} (hs : s ∈ Subgroup.center (GL (Fin 3) K))
    (hd : Matrix.GeneralLinearGroup.det s = 1) : ∃ u : Kˣ, s = sc u ∧ u ^ 3 = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u, rfl, by rw [← det_sc]; exact hd⟩

open Classical in
noncomputable def cubeRoots (K : Type) [Field K] : Finset K :=
  (Polynomial.nthRoots 3 (1 : K)).toFinset

open Classical in
theorem mem_cubeRoots {u : K} : u ∈ cubeRoots K ↔ u ^ 3 = 1 := by
  rw [cubeRoots, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]

open Classical in
theorem card_cubeRoots_le : (cubeRoots K).card ≤ 3 :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 (1 : K))

end Scalars

section Main

variable {E : Type} [Group E] {ρ : E →* Matrix.ProjGenLinGroup (Fin 3) K}
  {ℓ : E → GL (Fin 3) K}

theorem exists_conj_eq_sc (hℓd : ∀ x, Matrix.GeneralLinearGroup.det (ℓ x) = 1)
    (hℓm : ∀ x, Matrix.ProjGenLinGroup.mk (ℓ x) = ρ x) {x y : E} (hxy : x * y = y * x) :
    ∃ u : Kˣ, u ^ 3 = 1 ∧ ℓ x * ℓ y * (ℓ x)⁻¹ = sc u * ℓ y := by
  have hc : ℓ x * ℓ y * (ℓ x)⁻¹ * (ℓ y)⁻¹ ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hxy]; group
    have h2 : Matrix.ProjGenLinGroup.mk (ℓ x * ℓ y * (ℓ x)⁻¹ * (ℓ y)⁻¹) =
        ρ (x * y * x⁻¹ * y⁻¹) := by
      simp only [map_mul, map_inv, hℓm]
    rw [h2, h1, map_one]
  have hd : Matrix.GeneralLinearGroup.det (ℓ x * ℓ y * (ℓ x)⁻¹ * (ℓ y)⁻¹) = 1 := by
    simp only [map_mul, map_inv, hℓd, inv_one, mul_one]
  obtain ⟨u, hu, hu3⟩ := exists_sc_of_center hc hd
  refine ⟨u, hu3, ?_⟩
  calc ℓ x * ℓ y * (ℓ x)⁻¹ = (ℓ x * ℓ y * (ℓ x)⁻¹ * (ℓ y)⁻¹) * ℓ y := by group
    _ = sc u * ℓ y := by rw [hu]

theorem eq_of_inv_mul_mem_center (hρ : Function.Injective ρ)
    (hℓm : ∀ x, Matrix.ProjGenLinGroup.mk (ℓ x) = ρ x) {z z' : E}
    (h : (ℓ z)⁻¹ * ℓ z' ∈ Subgroup.center (GL (Fin 3) K)) : z = z' := by
  have := Matrix.ProjGenLinGroup.mk_eq_one.2 h
  rw [map_mul, map_inv, hℓm, hℓm, inv_mul_eq_one] at this
  exact hρ this

theorem ne_center_of_ne_one (hρ : Function.Injective ρ)
    (hℓm : ∀ x, Matrix.ProjGenLinGroup.mk (ℓ x) = ρ x) {x : E} (hx : x ≠ 1) :
    ℓ x ∉ Subgroup.center (GL (Fin 3) K) := by
  intro h
  apply hx
  apply hρ
  rw [map_one, ← hℓm]
  exact Matrix.ProjGenLinGroup.mk_eq_one.2 h

theorem card_le_nine_of_noncomm (hρ : Function.Injective ρ)
    (hℓd : ∀ x, Matrix.GeneralLinearGroup.det (ℓ x) = 1)
    (hℓm : ∀ x, Matrix.ProjGenLinGroup.mk (ℓ x) = ρ x) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hcomm : ∀ x y : E, x * y = y * x) {a b : E} (hab : ℓ a * ℓ b ≠ ℓ b * ℓ a) :
    Nat.card E ≤ 9 := by
  have h3 := three_ne_zero_of_cube_root hτ hτ1
  obtain ⟨ν, hν3, hν⟩ := exists_conj_eq_sc hℓd hℓm (hcomm a b)
  have hν1 : ν ≠ 1 := by
    rintro rfl
    apply hab
    have : ℓ a * ℓ b * (ℓ a)⁻¹ = ℓ b := by rw [hν, sc_one, one_mul]
    calc ℓ a * ℓ b = (ℓ a * ℓ b * (ℓ a)⁻¹) * ℓ a := by group
      _ = ℓ b * ℓ a := by rw [this]
  choose cA hcA3 hcA using fun z => exists_conj_eq_sc hℓd hℓm (hcomm z a)
  choose cB hcB3 hcB using fun z => exists_conj_eq_sc hℓd hℓm (hcomm z b)
  have hcA3' : ∀ z, ((cA z : Kˣ) : K) ^ 3 = 1 := fun z => by
    rw [← Units.val_pow_eq_pow_val, hcA3, Units.val_one]
  have hcB3' : ∀ z, ((cB z : Kˣ) : K) ^ 3 = 1 := fun z => by
    rw [← Units.val_pow_eq_pow_val, hcB3, Units.val_one]
  let Φ : E → cubeRoots K × cubeRoots K := fun z =>
    (⟨((cA z : Kˣ) : K), mem_cubeRoots.2 (hcA3' z)⟩, ⟨((cB z : Kˣ) : K), mem_cubeRoots.2 (hcB3' z)⟩)
  have hΦ : Function.Injective Φ := by
    intro z z' h
    have h1 : cA z = cA z' := Units.ext (congrArg (fun p : cubeRoots K × cubeRoots K => (p.1 : K)) h)
    have h2 : cB z = cB z' := Units.ext (congrArg (fun p : cubeRoots K × cubeRoots K => (p.2 : K)) h)
    have eA : ℓ z * ℓ a * (ℓ z)⁻¹ = ℓ z' * ℓ a * (ℓ z')⁻¹ := by rw [hcA z, hcA z', h1]
    have eB : ℓ z * ℓ b * (ℓ z)⁻¹ = ℓ z' * ℓ b * (ℓ z')⁻¹ := by rw [hcB z, hcB z', h2]
    refine eq_of_inv_mul_mem_center hρ hℓm (mem_center_of_commute_heis h3 hν3 hν1 hν _ ?_ ?_)
    · calc (ℓ z)⁻¹ * ℓ z' * ℓ a = (ℓ z)⁻¹ * (ℓ z' * ℓ a * (ℓ z')⁻¹) * ℓ z' := by group
        _ = (ℓ z)⁻¹ * (ℓ z * ℓ a * (ℓ z)⁻¹) * ℓ z' := by rw [eA]
        _ = ℓ a * ((ℓ z)⁻¹ * ℓ z') := by group
    · calc (ℓ z)⁻¹ * ℓ z' * ℓ b = (ℓ z)⁻¹ * (ℓ z' * ℓ b * (ℓ z')⁻¹) * ℓ z' := by group
        _ = (ℓ z)⁻¹ * (ℓ z * ℓ b * (ℓ z)⁻¹) * ℓ z' := by rw [eB]
        _ = ℓ b * ((ℓ z)⁻¹ * ℓ z') := by group
  calc Nat.card E ≤ Nat.card (cubeRoots K × cubeRoots K) := Nat.card_le_card_of_injective Φ hΦ
    _ = (cubeRoots K).card * (cubeRoots K).card := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 3 * 3 := Nat.mul_le_mul card_cubeRoots_le card_cubeRoots_le

theorem card_le_nine_of_comm (hρ : Function.Injective ρ)
    (hℓd : ∀ x, Matrix.GeneralLinearGroup.det (ℓ x) = 1)
    (hℓm : ∀ x, Matrix.ProjGenLinGroup.mk (ℓ x) = ρ x) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (h3 : ∀ x : E, x ^ 3 = 1) (hl : ∀ x y : E, ℓ x * ℓ y = ℓ y * ℓ x) : Nat.card E ≤ 9 := by
  have hcen : ∀ x, ℓ x ^ 3 ∈ Subgroup.center (GL (Fin 3) K) := fun x => by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_pow, hℓm, ← map_pow, h3, map_one]
  have hdt : ∀ x, Matrix.GeneralLinearGroup.det (ℓ x ^ 3) = 1 := fun x => by
    rw [map_pow, hℓd, one_pow]
  choose w hw hw3 using fun x => exists_sc_of_center (hcen x) (hdt x)
  have hmul : ∀ x y : E, ℓ (x * y) ^ 3 = ℓ x ^ 3 * ℓ y ^ 3 := by
    intro x y
    have hs : (ℓ x * ℓ y)⁻¹ * ℓ (x * y) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [← Matrix.ProjGenLinGroup.mk_eq_one]
      simp [map_mul, map_inv, hℓm]
    have hsd : Matrix.GeneralLinearGroup.det ((ℓ x * ℓ y)⁻¹ * ℓ (x * y)) = 1 := by
      simp [map_mul, map_inv, hℓd]
    obtain ⟨u, hu, hu3⟩ := exists_sc_of_center hs hsd
    have hxy : ℓ (x * y) = ℓ x * ℓ y * sc u := by rw [← hu]; group
    have hs3 : (sc u : GL (Fin 3) K) ^ 3 = 1 := by rw [← sc_pow, hu3, sc_one]
    rw [hxy, Commute.mul_pow (commute_sc u _).symm, hs3, mul_one, Commute.mul_pow (hl x y)]
  let lamU : E →* Kˣ := MonoidHom.mk' w fun x y =>
    sc_injective (by rw [sc_mul, ← hw, ← hw, ← hw, hmul])
  have hlam : ∀ x, lamU x = w x := fun x => rfl
  have hrange : Nat.card lamU.range ≤ 3 := by
    let ψ : lamU.range → cubeRoots K := fun r => ⟨(r.1 : K), mem_cubeRoots.2 (by
      obtain ⟨x, hx⟩ := r.2
      rw [← hx, ← Units.val_pow_eq_pow_val, hlam, hw3, Units.val_one])⟩
    have hψ : Function.Injective ψ := fun r r' h => Subtype.ext (Units.ext (congrArg Subtype.val h))
    calc Nat.card lamU.range ≤ Nat.card (cubeRoots K) := Nat.card_le_card_of_injective ψ hψ
      _ = (cubeRoots K).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ 3 := card_cubeRoots_le
  have hker : Nat.card lamU.ker ≤ 3 := by
    by_cases htriv : ∀ y ∈ lamU.ker, y = 1
    · have hsub : Subsingleton lamU.ker :=
        ⟨fun a b => Subtype.ext ((htriv _ a.2).trans (htriv _ b.2).symm)⟩
      let ψ : lamU.ker → cubeRoots K := fun _ => ⟨1, mem_cubeRoots.2 (one_pow 3)⟩
      calc Nat.card lamU.ker ≤ Nat.card (cubeRoots K) :=
            Nat.card_le_card_of_injective ψ fun a b _ => Subsingleton.elim a b
        _ = (cubeRoots K).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ ≤ 3 := card_cubeRoots_le
    · push Not at htriv
      obtain ⟨x0, hx0, hx01⟩ := htriv
      have hker3 : ∀ y ∈ lamU.ker, ℓ y ^ 3 = 1 := fun y hy => by
        have hy' : w y = 1 := MonoidHom.mem_ker.1 hy
        rw [hw y, hy', sc_one]
      have hdet : ∀ y, (ℓ y : Matrix (Fin 3) (Fin 3) K).det = 1 := fun y => by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, hℓd, Units.val_one]
      obtain ⟨f, hf1, hf2⟩ := exists_ratio hτ hτ1 (hker3 x0 hx0) (hdet x0)
        (ne_center_of_ne_one hρ hℓm hx01)
      let ψ : lamU.ker → cubeRoots K := fun y =>
        ⟨f (ℓ y), mem_cubeRoots.2 (hf1 (ℓ y) (hl y x0) (hker3 y y.2) (hdet y))⟩
      have hψ : Function.Injective ψ := by
        intro y y' h
        have h1 : f (ℓ y) = f (ℓ y') := congrArg Subtype.val h
        exact Subtype.ext (eq_of_inv_mul_mem_center hρ hℓm
          (hf2 (ℓ y) (ℓ y') (hl y x0) (hker3 y y.2) (hdet y) (hl y' x0) (hker3 y' y'.2) (hdet y')
            h1))
      calc Nat.card lamU.ker ≤ Nat.card (cubeRoots K) := Nat.card_le_card_of_injective ψ hψ
        _ = (cubeRoots K).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ ≤ 3 := card_cubeRoots_le
  calc Nat.card E = Nat.card lamU.ker * Nat.card lamU.range :=
        (Subgroup.card_ker_mul_card_range lamU).symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker hrange

theorem card_le_nine (hρ : Function.Injective ρ) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hcomm : ∀ x y : E, x * y = y * x) (h3 : ∀ x : E, x ^ 3 = 1)
    (hlift : ∀ x : E, ∃ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      Matrix.ProjGenLinGroup.mk g = ρ x) : Nat.card E ≤ 9 := by
  choose ℓ hℓd hℓm using hlift
  have hℓd' : ∀ x, Matrix.GeneralLinearGroup.det (ℓ x) = 1 := fun x =>
    Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hℓd x, Units.val_one])
  by_cases hl : ∀ x y : E, ℓ x * ℓ y = ℓ y * ℓ x
  · exact card_le_nine_of_comm hρ hℓd' hℓm hτ hτ1 h3 hl
  · push Not at hl
    obtain ⟨a, b, hab⟩ := hl
    exact card_le_nine_of_noncomm hρ hℓd' hℓm hτ hτ1 hcomm hab

end Main

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.K32A
