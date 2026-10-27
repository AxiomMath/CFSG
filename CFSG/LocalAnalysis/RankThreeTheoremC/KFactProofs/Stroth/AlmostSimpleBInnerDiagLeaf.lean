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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

private theorem eq_zero_of_commute_of_diagonal {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι K W)
    (a n : Module.End K W) (μ : ι → K) (hμ : Function.Injective μ)
    (haB : ∀ i, a (B i) = μ i • B i) (hna : n * a = a * n) (hnn : n * n = 0) : n = 0 := by
  have hD : LinearMap.toMatrix B B a = Matrix.diagonal μ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [LinearMap.toMatrix_apply, haB]
    · simp [LinearMap.toMatrix_apply, haB, Matrix.diagonal_apply, Finsupp.single_apply, hij,
        Ne.symm hij]
  set N := LinearMap.toMatrix B B n with hN
  have hcomm : N * Matrix.diagonal μ = Matrix.diagonal μ * N := by
    rw [← hD, hN, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, hna]
  have hsq : N * N = 0 := by
    rw [hN, ← LinearMap.toMatrix_mul, hnn, map_zero]
  have hoff : ∀ i j, i ≠ j → N i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hcomm i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h' : N i j * (μ j - μ i) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact h0
    · exact absurd (hμ (sub_eq_zero.mp h0).symm) hij
  have hdiag : ∀ i, N i i = 0 := by
    intro i
    have h := congrFun (congrFun hsq i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · exact mul_self_eq_zero.mp (by simpa using h)
    · intro k _ hk
      rw [hoff i k (Ne.symm hk), zero_mul]
    · simp
  apply (LinearMap.toMatrix B B).injective
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa using hdiag i
  · simpa using hoff i j hij

private theorem generalLinearGroup_injective {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] (a : LinearMap.GeneralLinearGroup K W) :
    Function.Injective (a : Module.End K W) :=
  a.toLinearEquiv.injective

theorem eq_one_of_sq_eq_one_of_commute_of_conj_smul {K : Type*} [Field K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hW : Module.finrank K W = 3) {ζ : K} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    {a g t : LinearMap.GeneralLinearGroup K W}
    (hg : (g : Module.End K W) * (a : Module.End K W) =
      ζ • ((a : Module.End K W) * (g : Module.End K W)))
    (ht : (t : Module.End K W) * (a : Module.End K W) = (a : Module.End K W) * (t : Module.End K W))
    (ht2 : t ^ 2 = 1) : t = 1 := by
  by_contra htne
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ3
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply hζ1
    have h' : ζ ^ 2 * ζ = 1 := by linear_combination hζ3
    rwa [h, one_mul] at h'
  set n : Module.End K W := (t : Module.End K W) - 1 with hn
  have hxx : ∀ x : W, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have htt : ∀ x : W, (t : Module.End K W) ((t : Module.End K W) x) = x := by
    intro x
    have h2 : (t : Module.End K W) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht2, Units.val_one]
    have := congrArg (fun f : Module.End K W => f x) h2
    simpa [pow_two] using this
  have hnn : n * n = 0 := by
    ext x
    have h : n (n x) = (x + x) - ((t : Module.End K W) x + (t : Module.End K W) x) := by
      simp only [hn, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub, htt]
      abel
    simp [Module.End.mul_apply, h, hxx]
  have hna : n * (a : Module.End K W) = (a : Module.End K W) * n := by
    simp only [hn, sub_mul, mul_sub, one_mul, mul_one, ht]
  have hn0 : n ≠ 0 := by
    intro h
    exact htne (Units.ext (by simpa [hn, sub_eq_zero] using h))
  have hker : LinearMap.range n ≤ LinearMap.ker n := by
    rw [LinearMap.range_le_ker_iff, ← Module.End.mul_eq_comp]
    exact hnn
  have hrank : Module.finrank K (LinearMap.range n) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker n
    have h2 : Module.finrank K (LinearMap.range n) ≤ Module.finrank K (LinearMap.ker n) :=
      Submodule.finrank_mono hker
    have h3 : 1 ≤ Module.finrank K (LinearMap.range n) := by
      rw [Submodule.one_le_finrank_iff]
      intro h
      exact hn0 (LinearMap.range_eq_bot.mp h)
    omega
  obtain ⟨⟨u, hu⟩, hu0, hspan⟩ := finrank_eq_one_iff'.mp hrank
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hAu : (a : Module.End K W) u ∈ LinearMap.range n := by
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hu
    refine LinearMap.mem_range.mpr ⟨(a : Module.End K W) w, ?_⟩
    rw [← hw]
    have := congrArg (fun f : Module.End K W => f w) hna
    simpa [Module.End.mul_apply] using this
  obtain ⟨μ, hμ⟩ := hspan ⟨(a : Module.End K W) u, hAu⟩
  have hau : (a : Module.End K W) u = μ • u := by
    have := congrArg Subtype.val hμ
    simpa using this.symm
  have hμ0 : μ ≠ 0 := by
    intro h
    apply hu0'
    apply generalLinearGroup_injective a
    rw [hau, h, zero_smul, map_zero]
  set A : Module.End K W := (a : Module.End K W)
  set G : Module.End K W := (g : Module.End K W)
  have hζ' : ζ ^ 2 * ζ = 1 := by linear_combination hζ3
  have hGA : ∀ (x : W) (c : K), A x = c • x → A (G x) = (ζ ^ 2 * c) • G x := by
    intro x c hx
    have h1 : G (A x) = ζ • A (G x) := by
      have := congrArg (fun f : Module.End K W => f x) hg
      simpa [Module.End.mul_apply] using this
    rw [hx, map_smul] at h1
    calc A (G x) = (ζ ^ 2 * ζ) • A (G x) := by rw [hζ', one_smul]
      _ = ζ ^ 2 • (ζ • A (G x)) := (smul_smul _ _ _).symm
      _ = ζ ^ 2 • (c • G x) := by rw [← h1]
      _ = (ζ ^ 2 * c) • G x := smul_smul _ _ _
  have hGinj : Function.Injective G := generalLinearGroup_injective g
  have hG0 : ∀ x : W, x ≠ 0 → G x ≠ 0 := fun x hx h => hx (hGinj (h.trans (map_zero G).symm))
  have hζ4 : ζ ^ 2 * (ζ ^ 2 * μ) = ζ * μ := by linear_combination (ζ * μ) * hζ3
  let v : Fin 3 → W := ![u, G u, G (G u)]
  let e : Fin 3 → K := ![μ, ζ ^ 2 * μ, ζ * μ]
  have hAv : ∀ i, A (v i) = e i • v i := by
    intro i
    fin_cases i
    · simpa [v, e] using hau
    · simpa [v, e] using hGA u μ hau
    · simpa [v, e, hζ4] using hGA (G u) (ζ ^ 2 * μ) (hGA u μ hau)
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [v] using hu0'
    · simpa [v] using hG0 u hu0'
    · simpa [v] using hG0 (G u) (hG0 u hu0')
  have h01 : μ ≠ ζ ^ 2 * μ := fun h =>
    hζ2 (mul_right_cancel₀ hμ0 (h.symm.trans (one_mul μ).symm))
  have h02 : μ ≠ ζ * μ := fun h =>
    hζ1 (mul_right_cancel₀ hμ0 (h.symm.trans (one_mul μ).symm))
  have h12 : ζ ^ 2 * μ ≠ ζ * μ := fun h =>
    hζ1 (mul_left_cancel₀ hζ0 (by
      have := mul_right_cancel₀ hμ0 h
      linear_combination this))
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd hij h01
      | exact absurd hij.symm h01
      | exact absurd hij h02
      | exact absurd hij.symm h02
      | exact absurd hij h12
      | exact absurd hij.symm h12
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' A e he v fun i =>
      Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hAv i), hv0 i⟩
  let B : Module.Basis (Fin 3) K W :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp [hW])
  have hB : ∀ i, B i = v i := fun i => by simp [B]
  exact hn0 (eq_zero_of_commute_of_diagonal B A n e he (fun i => by rw [hB]; exact hAv i) hna hnn)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
