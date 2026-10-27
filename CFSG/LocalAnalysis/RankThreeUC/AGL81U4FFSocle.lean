module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.RankThreeUC

lemma two_nsmul_eq_zero_of_charP {K R : Type*} [Field K] [CharP K 2] [AddCommGroup R]
    [Module K R] (x : R) : (2 : ℕ) • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

lemma exists_linearMap_apply_eq_one {K R : Type*} [Field K] [AddCommGroup R] [Module K R]
    {v : R} (hv : v ≠ 0) : ∃ f : R →ₗ[K] K, f v = 1 := by
  have hex : ∃ φ : Module.Dual K R, φ v ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp h)
  obtain ⟨φ, hφ⟩ := hex
  refine ⟨(φ v)⁻¹ • φ, ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]

def evalAtVec {K R : Type*} [Field K] [AddCommGroup R] [Module K R] (v : R) :
    (R →ₗ[K] K) →ₗ[K] K where
  toFun g := g v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma natCard_ker_evalAtVec {K R : Type*} [Field K] [AddCommGroup R] [Module K R]
    [Module.Finite K R] {v : R} {f : R →ₗ[K] K} (hf : f v = 1) :
    Nat.card (LinearMap.ker (evalAtVec (K := K) v)) = Nat.card K ^ (Module.finrank K R - 1) := by
  have hsurj : Function.Surjective (evalAtVec (K := K) v) := fun c =>
    ⟨c • f, by
      change (c • f) v = c
      rw [LinearMap.smul_apply, hf, smul_eq_mul, mul_one]⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker (evalAtVec (K := K) v)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Subspace.dual_finrank_eq] at hrank
  have hk : Module.finrank K (LinearMap.ker (evalAtVec (K := K) v)) = Module.finrank K R - 1 := by
    omega
  have hcard := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (evalAtVec (K := K) v))
  rw [hcard, hk]

lemma eq_of_forall_apply_sub_eq_zero {K R : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup R] [Module K R] [Module.Finite K R] (𝒟 : Subgroup (R ≃ₗ[K] R))
    (hcomm : ∀ d ∈ 𝒟, ∀ e ∈ 𝒟, d * e = e * d) (h2 : ∀ d ∈ 𝒟, d * d = 1)
    {v : R} (hline : ∀ x : R, (∀ d ∈ 𝒟, d x = x) → ∃ c : K, x = c • v)
    {f : R →ₗ[K] K} (hf : f v = 1) {d d' : R ≃ₗ[K] R} (hd : d ∈ 𝒟) (hd' : d' ∈ 𝒟)
    (hdiff : ∀ x, f (d x - d' x) = 0) : d = d' := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a : R →ₗ[K] R, ∀ x, a x = d x - d' x :=
    ⟨d.toLinearMap - d'.toLinearMap, fun x => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, d y ≠ d' y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hne (LinearEquiv.ext h)
  have hay : a y ≠ 0 := by
    rw [ha y]
    exact sub_ne_zero.mpr hy
  have hfa : ∀ z, f (a z) = 0 := fun z => by
    rw [ha z]
    exact hdiff z
  have hcomm' : ∀ e ∈ 𝒟, ∀ w : R, e (a w) = a (e w) := by
    intro e he w
    have h1 : e (d w) = d (e w) := congrArg (fun g : R ≃ₗ[K] R => g w) (hcomm e he d hd)
    have h1' : e (d' w) = d' (e w) := congrArg (fun g : R ≃ₗ[K] R => g w) (hcomm e he d' hd')
    rw [ha, ha, map_sub, h1, h1']
  have hinv : ∀ e ∈ 𝒟, ∀ x ∈ LinearMap.range a, e x ∈ LinearMap.range a := by
    intro e he x hx
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hx
    rw [hcomm' e he w]
    exact LinearMap.mem_range_self a (e w)
  haveI : Finite R := Module.finite_of_finite K
  letI : MulAction 𝒟 (LinearMap.range a) :=
    { smul := fun e m => ⟨(e : R ≃ₗ[K] R) (m : R), hinv (e : R ≃ₗ[K] R) e.2 (m : R) m.2⟩
      one_smul := fun m => Subtype.ext rfl
      mul_smul := fun g h m => Subtype.ext rfl }
  have hP : IsPGroup 2 𝒟 := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_two] using h2 (g : R ≃ₗ[K] R) g.2
  have hu : (⟨a y, LinearMap.mem_range_self a y⟩ : LinearMap.range a) ≠ 0 := by
    intro h0
    exact hay (congrArg Subtype.val h0)
  have h2u : (2 : ℕ) • (⟨a y, LinearMap.mem_range_self a y⟩ : LinearMap.range a) = 0 := by
    apply Subtype.ext
    simpa using two_nsmul_eq_zero_of_charP (K := K) (a y)
  have hdvd : 2 ∣ Nat.card (LinearMap.range a) := by
    have h := addOrderOf_dvd_natCard (⟨a y, LinearMap.mem_range_self a y⟩ : LinearMap.range a)
    rwa [addOrderOf_eq_prime h2u hu] at h
  have hfix0 : (⟨0, Submodule.zero_mem _⟩ : LinearMap.range a) ∈
      MulAction.fixedPoints 𝒟 (LinearMap.range a) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    show (g : R ≃ₗ[K] R) 0 = 0
    exact map_zero _
  obtain ⟨b, hb, hab⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (LinearMap.range a) hdvd hfix0
  have hbfix : ∀ e ∈ 𝒟, e (b : R) = b := by
    intro e he
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨e, he⟩)
  have hw0 : (b : R) ≠ 0 := by
    intro h0
    exact hab (Subtype.ext h0.symm)
  obtain ⟨c, hc⟩ := hline (b : R) hbfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw0
    rw [hc, zero_smul]
  have hvM : v ∈ LinearMap.range a := by
    have hv' : v = c⁻¹ • (b : R) := by
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hv']
    exact (LinearMap.range a).smul_mem c⁻¹ b.2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hvM
  have hfv : f v = 0 := by
    rw [← hz]
    exact hfa z
  rw [hf] at hfv
  exact one_ne_zero hfv

theorem card_le_pow_of_fixed_line {K R : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup R] [Module K R] [Module.Finite K R] (𝒟 : Subgroup (R ≃ₗ[K] R))
    (hcomm : ∀ d ∈ 𝒟, ∀ e ∈ 𝒟, d * e = e * d) (h2 : ∀ d ∈ 𝒟, d * d = 1)
    {v : R} (hv : v ≠ 0) (hvfix : ∀ d ∈ 𝒟, d v = v)
    (hline : ∀ x : R, (∀ d ∈ 𝒟, d x = x) → ∃ c : K, x = c • v) :
    Nat.card 𝒟 ≤ Nat.card K ^ (Module.finrank K R - 1) := by
  obtain ⟨f, hf⟩ := exists_linearMap_apply_eq_one (K := K) hv
  let Φ : 𝒟 → LinearMap.ker (evalAtVec (K := K) v) := fun d =>
    ⟨f ∘ₗ ((d : R ≃ₗ[K] R).toLinearMap - LinearMap.id), by
      rw [LinearMap.mem_ker]
      change f ((d : R ≃ₗ[K] R) v - v) = 0
      rw [hvfix _ d.2, sub_self, map_zero]⟩
  have hΦ : Function.Injective Φ := by
    intro d d' hdd
    have hfun : ∀ x, f ((d : R ≃ₗ[K] R) x - (d' : R ≃ₗ[K] R) x) = 0 := by
      intro x
      have hx : f ((d : R ≃ₗ[K] R) x - x) = f ((d' : R ≃ₗ[K] R) x - x) :=
        congrArg (fun g : R →ₗ[K] K => g x) (congrArg Subtype.val hdd)
      rw [show (d : R ≃ₗ[K] R) x - (d' : R ≃ₗ[K] R) x
          = ((d : R ≃ₗ[K] R) x - x) - ((d' : R ≃ₗ[K] R) x - x) by abel,
        map_sub, hx, sub_self]
    exact Subtype.ext (eq_of_forall_apply_sub_eq_zero 𝒟 hcomm h2 hline hf d.2 d'.2 hfun)
  haveI : Finite (LinearMap.ker (evalAtVec (K := K) v)) := Module.finite_of_finite K
  calc Nat.card 𝒟 ≤ Nat.card (LinearMap.ker (evalAtVec (K := K) v)) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card K ^ (Module.finrank K R - 1) := natCard_ker_evalAtVec hf

end CFSG.LocalAnalysis.RankThreeUC
