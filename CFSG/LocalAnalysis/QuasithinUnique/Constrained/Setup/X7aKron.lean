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
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped Matrix

section Kron

variable {K : Type} [Field K] {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

theorem kron_sub_one_mulVec_apply (A : Matrix α α K) (U : Matrix β β K) (z : α × β → K) (x : α)
    (i : β) :
    ((Matrix.kroneckerMap (· * ·) A U - 1).mulVec z) (x, i) =
      ∑ b, U i b * (A.mulVec (fun x' => z (x', b))) x - z (x, i) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

theorem rank_kron_free (A A' : Matrix α α K) (hA : A * A' = 1) (U : Matrix β β K) (X : Finset β)
    (hU : ∀ c : β → K, (∀ b ∉ X, c b = 0) → (∀ i ∉ X, ∑ b, U i b * c b = 0) → c = 0) :
    X.card * Fintype.card α ≤ (Matrix.kroneckerMap (· * ·) A U - 1).rank := by
  classical
  have hA' : A' * A = 1 := mul_eq_one_comm.mp hA
  set D := Matrix.kroneckerMap (· * ·) A U - 1 with hD
  let ext : (X → α → K) →ₗ[K] (α × β → K) :=
    LinearMap.pi fun p : α × β =>
      if h : p.2 ∈ X then (LinearMap.proj p.1 : (α → K) →ₗ[K] K) ∘ₗ
        (LinearMap.proj (⟨p.2, h⟩ : X) : (X → α → K) →ₗ[K] (α → K)) else 0
  have hext : ∀ (y : X → α → K) (x : α) (b : β), ext y (x, b) =
      if h : b ∈ X then y ⟨b, h⟩ x else 0 := by
    intro y x b
    simp only [ext, LinearMap.pi_apply]
    by_cases h : b ∈ X <;> simp [h]
  let Φ : (X → α → K) →ₗ[K] (α × β → K) := D.mulVecLin ∘ₗ ext
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : D.mulVec (ext y) = 0 := hy
    have hcol : ∀ x : α, (fun b => if b ∈ X then (A.mulVec (fun x' => ext y (x', b))) x else 0) =
        0 := by
      intro x
      refine hU _ (fun b hb => by simp [hb]) (fun i hi => ?_)
      have h1 := congrFun hy' (x, i)
      rw [kron_sub_one_mulVec_apply] at h1
      simp only [Pi.zero_apply] at h1
      have h2 : ext y (x, i) = 0 := by rw [hext]; simp [hi]
      rw [h2, sub_zero] at h1
      refine Eq.trans ?_ h1
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b ∈ X
      · simp [hb]
      · have : (fun x' => ext y (x', b)) = 0 := by
          funext x'
          rw [hext]
          simp [hb]
        rw [this]
        simp [hb]
    funext ⟨b, hb⟩ x
    have h4 : A.mulVec (fun x' => ext y (x', b)) = 0 := by
      funext x₀
      have := congrFun (hcol x₀) b
      simpa [hb] using this
    have h5 : (fun x' => ext y (x', b)) = 0 := by
      have := congrArg (fun v => A'.mulVec v) h4
      simpa [Matrix.mulVec_mulVec, hA'] using this
    have h6 := congrFun h5 x
    rw [hext] at h6
    simpa [hb] using h6
  have hrank : Module.finrank K (X → α → K) ≤ D.rank := by
    rw [Matrix.rank]
    calc Module.finrank K (X → α → K) = Module.finrank K (LinearMap.range Φ) :=
          (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ Module.finrank K (LinearMap.range D.mulVecLin) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hdim : Module.finrank K (X → α → K) = X.card * Fintype.card α := by
    simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
  rw [← hdim]
  exact hrank

theorem rank_kron_free_one (A A' : Matrix α α K) (hA : A * A' = 1) (U : Matrix β β K)
    (f g h : β) (hfh : f ≠ h) (hgf : g ≠ f) (hgh : g ≠ h) (h1 : U g f = 1) (h2 : U g h = 0)
    (h3 : U h f = 0) (h4 : U h h = 1) :
    Fintype.card α + (A - 1).rank ≤ (Matrix.kroneckerMap (· * ·) A U - 1).rank := by
  classical
  have hA' : A' * A = 1 := mul_eq_one_comm.mp hA
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (A - 1).mulVecLin)
  set D := Matrix.kroneckerMap (· * ·) A U - 1 with hD
  let ext : ((α → K) × C) →ₗ[K] (α × β → K) :=
    LinearMap.pi fun p : α × β =>
      if p.2 = f then (LinearMap.proj p.1 : (α → K) →ₗ[K] K) ∘ₗ LinearMap.fst K (α → K) C
      else if p.2 = h then (LinearMap.proj p.1 : (α → K) →ₗ[K] K) ∘ₗ
        (C.subtype ∘ₗ LinearMap.snd K (α → K) C) else 0
  have hext : ∀ (y : (α → K) × C) (x : α) (b : β), ext y (x, b) =
      if b = f then y.1 x else if b = h then (y.2 : α → K) x else 0 := by
    intro y x b
    simp only [ext, LinearMap.pi_apply]
    by_cases hb : b = f
    · simp [hb]
    · by_cases hb' : b = h <;> simp [hb, hb', hfh.symm]
  let Φ : ((α → K) × C) →ₗ[K] (α × β → K) := D.mulVecLin ∘ₗ ext
  have hslice : ∀ (y : (α → K) × C) (b : β), (fun x' => ext y (x', b)) =
      if b = f then y.1 else if b = h then (y.2 : α → K) else 0 := by
    intro y b
    funext x'
    rw [hext]
    by_cases hb : b = f
    · simp [hb]
    · by_cases hb' : b = h <;> simp [hb, hb', hfh.symm]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : D.mulVec (ext y) = 0 := hy
    have hg : A.mulVec y.1 = 0 := by
      funext x
      have e1 := congrFun hy' (x, g)
      rw [kron_sub_one_mulVec_apply] at e1
      simp only [Pi.zero_apply] at e1
      have e2 : ext y (x, g) = 0 := by rw [hext]; simp [hgf, hgh]
      rw [e2, sub_zero] at e1
      rw [Finset.sum_eq_add f h hfh (fun c _ hc => by
        rw [hslice]
        simp [hc.1, hc.2]) (fun hn => absurd (Finset.mem_univ f) hn)
        (fun hn => absurd (Finset.mem_univ h) hn), hslice, hslice] at e1
      simpa [h1, h2, hfh.symm] using e1
    have hy1 : y.1 = 0 := by
      have := congrArg (fun v => A'.mulVec v) hg
      simpa [Matrix.mulVec_mulVec, hA'] using this
    have hh : (A - 1).mulVec (y.2 : α → K) = 0 := by
      funext x
      have e1 := congrFun hy' (x, h)
      rw [kron_sub_one_mulVec_apply] at e1
      simp only [Pi.zero_apply] at e1
      have e2 : ext y (x, h) = (y.2 : α → K) x := by rw [hext]; simp [hfh.symm]
      rw [e2] at e1
      rw [Finset.sum_eq_add f h hfh (fun c _ hc => by
        rw [hslice]
        simp [hc.1, hc.2]) (fun hn => absurd (Finset.mem_univ f) hn)
        (fun hn => absurd (Finset.mem_univ h) hn), hslice, hslice] at e1
      simp only [hfh.symm, h3, h4, hy1, zero_mul, one_mul, Matrix.mulVec_zero, Pi.zero_apply,
        zero_add, ↓reduceIte] at e1
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      simpa using e1
    have hy2 : y.2 = 0 := by
      have hmem : (y.2 : α → K) ∈ LinearMap.ker (A - 1).mulVecLin := by
        rw [LinearMap.mem_ker]
        exact hh
      have : (y.2 : α → K) ∈ LinearMap.ker (A - 1).mulVecLin ⊓ (C : Submodule K (α → K)) :=
        ⟨hmem, y.2.2⟩
      rw [hC.inf_eq_bot] at this
      exact Subtype.ext (by simpa using this)
    exact Prod.ext hy1 hy2
  have hrank : Module.finrank K ((α → K) × C) ≤ D.rank := by
    rw [Matrix.rank]
    calc Module.finrank K ((α → K) × C) = Module.finrank K (LinearMap.range Φ) :=
          (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ Module.finrank K (LinearMap.range D.mulVecLin) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hC1 : Module.finrank K (LinearMap.ker (A - 1).mulVecLin) + Module.finrank K C =
      Module.finrank K (α → K) := Submodule.finrank_add_eq_of_isCompl hC
  have hC2 := LinearMap.finrank_range_add_finrank_ker (A - 1).mulVecLin
  have hdim : Module.finrank K ((α → K) × C) = Fintype.card α + (A - 1).rank := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Matrix.rank]
    have : Module.finrank K C = Module.finrank K (LinearMap.range (A - 1).mulVecLin) := by
      rw [Module.finrank_fintype_fun_eq_card] at hC1 hC2
      omega
    rw [this]
  rw [← hdim]
  exact hrank

end Kron

end CFSG.QuasithinUnique.Setup.X7a
