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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.A5.Kc3Lin3

open Module

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem arith_aux (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 3) : (3 - j) * i ≤ 2 := by
  interval_cases j <;> simp <;> omega

theorem prod_zero_of_dim_three (hW : finrank F W = 3) {N M : W →ₗ[F] W} (hN : N ∘ₗ N = 0)
    (hM : M ∘ₗ M = 0) (hNM : N ∘ₗ M = M ∘ₗ N) : N ∘ₗ M = 0 := by
  by_contra hne
  have hrN : finrank F (LinearMap.range N) ≤ 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker N
    have h2 : LinearMap.range N ≤ LinearMap.ker N := by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.mem_ker.2 (by simpa using LinearMap.congr_fun hN x)
    have h3 := Submodule.finrank_mono h2
    omega
  have hP : LinearMap.range (N ∘ₗ M) ≠ ⊥ := by
    intro h
    exact hne (LinearMap.range_eq_bot.1 h)
  have hle : LinearMap.range (N ∘ₗ M) ≤ LinearMap.range N := LinearMap.range_comp_le_range M N
  have hpos : 1 ≤ finrank F (LinearMap.range (N ∘ₗ M)) := by
    by_contra h
    apply hP
    exact Submodule.finrank_eq_zero.1 (by omega)
  have heq : LinearMap.range (N ∘ₗ M) = LinearMap.range N :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hle2 : LinearMap.range N ≤ LinearMap.range M := by
    rw [← heq, hNM]
    exact LinearMap.range_comp_le_range N M
  have hle3 : LinearMap.range M ≤ LinearMap.ker M := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.2 (by simpa using LinearMap.congr_fun hM x)
  apply hne
  rw [hNM]
  ext w
  have : N w ∈ LinearMap.ker M := hle3 (hle2 ⟨w, rfl⟩)
  simpa using this

theorem finrank_le_two (hW : finrank F W = 3) (𝒲 : Submodule F (W →ₗ[F] W))
    (h0 : ∀ N ∈ 𝒲, ∀ M ∈ 𝒲, N ∘ₗ M = 0) : finrank F 𝒲 ≤ 2 := by
  classical
  set I : Submodule F W := ⨆ N : 𝒲, LinearMap.range (N : W →ₗ[F] W) with hI
  set J : Submodule F W := ⨅ N : 𝒲, LinearMap.ker (N : W →ₗ[F] W) with hJ
  have hIJ : I ≤ J := by
    refine iSup_le fun N x hx => ?_
    refine (Submodule.mem_iInf _).2 fun M => ?_
    obtain ⟨w, rfl⟩ := hx
    have := LinearMap.congr_fun (h0 M M.2 N N.2) w
    simpa using this
  have hNI : ∀ N : 𝒲, ∀ w, (N : W →ₗ[F] W) w ∈ I := fun N w =>
    (le_iSup (fun N : 𝒲 => LinearMap.range (N : W →ₗ[F] W)) N) ⟨w, rfl⟩
  have hJN : ∀ N : 𝒲, ∀ x ∈ J, (N : W →ₗ[F] W) x = 0 := fun N x hx =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hx N)
  let Φ : 𝒲 →ₗ[F] ((W ⧸ J) →ₗ[F] I) :=
    { toFun := fun N => J.liftQ ((N : W →ₗ[F] W).codRestrict I (hNI N))
        (fun x hx => LinearMap.mem_ker.2 (Subtype.ext (hJN N x hx)))
      map_add' := fun N M => by
        ext w
        rfl
      map_smul' := fun c N => by
        ext w
        rfl }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro N hN
    apply Subtype.ext
    ext w
    have := LinearMap.congr_fun hN (Submodule.Quotient.mk w)
    have h2 := congrArg Subtype.val this
    simpa [Φ] using h2
  have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_linearMap] at h1
  have h2 := Submodule.finrank_quotient_add_finrank J
  have h3 := Submodule.finrank_mono hIJ
  have h4 : finrank F J ≤ 3 := by
    have := Submodule.finrank_le J
    omega
  have h5 : finrank F (W ⧸ J) = 3 - finrank F J := by omega
  rw [h5] at h1
  have h6 := arith_aux (finrank F I) (finrank F J) h3 h4
  omega

end CFSG.QuasithinUnique.A5.Kc3Lin3
