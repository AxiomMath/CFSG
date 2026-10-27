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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
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

namespace CFSG.LargeExtraspecial.GLR

open Module

variable (F : Type*) [Field F]

abbrev NilModel (k m : ℕ) : Type _ := (Fin k → F) × (Fin m → F) × (Fin k → F)

@[expose] def nilModelMap (k m : ℕ) : NilModel F k m →ₗ[F] NilModel F k m :=
  LinearMap.inr F (Fin k → F) ((Fin m → F) × (Fin k → F)) ∘ₗ
    LinearMap.inr F (Fin m → F) (Fin k → F) ∘ₗ
      LinearMap.fst F (Fin k → F) ((Fin m → F) × (Fin k → F))

@[simp]
theorem nilModelMap_apply (k m : ℕ) (w : NilModel F k m) : nilModelMap F k m w = (0, 0, w.1) := rfl

variable {F} {V : Type*} [AddCommGroup V] [Module F V]

theorem range_le_ker_of_comp_eq_zero {N : V →ₗ[F] V} (hN : N ∘ₗ N = 0) :
    LinearMap.range N ≤ LinearMap.ker N := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hN, LinearMap.zero_apply]

variable [FiniteDimensional F V]

theorem two_mul_finrank_range_le_of_comp_eq_zero {N : V →ₗ[F] V} (hN : N ∘ₗ N = 0) :
    2 * finrank F (LinearMap.range N) ≤ finrank F V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker N
  have h2 := Submodule.finrank_mono (range_le_ker_of_comp_eq_zero hN)
  omega

theorem exists_linearEquiv_nilModel {N : V →ₗ[F] V} (hN : N ∘ₗ N = 0) {k m : ℕ}
    (hk : finrank F (LinearMap.range N) = k) (hm : finrank F V = 2 * k + m) :
    ∃ e : NilModel F k m ≃ₗ[F] V, ∀ w, N (e w) = e (nilModelMap F k m w) := by
  classical
  have hIK := range_le_ker_of_comp_eq_zero hN
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker N)
  have hCdim : finrank F C = k := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    omega
  set I' : Submodule F (LinearMap.ker N) := (LinearMap.range N).comap (LinearMap.ker N).subtype
    with hI'
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl I'
  have hI'dim : finrank F I' = k := by
    rw [← hk]
    exact (Submodule.comapSubtypeEquivOfLe hIK).finrank_eq
  have hDdim : finrank F D = m := by
    have := Submodule.finrank_add_eq_of_isCompl hD
    omega
  let c : (Fin k → F) ≃ₗ[F] C :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hCdim, Module.finrank_fin_fun])
  let d : (Fin m → F) ≃ₗ[F] D :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hDdim, Module.finrank_fin_fun])
  let f : NilModel F k m →ₗ[F] V :=
    (C.subtype ∘ₗ c.toLinearMap).coprod
      (((LinearMap.ker N).subtype ∘ₗ D.subtype ∘ₗ d.toLinearMap).coprod
        (N ∘ₗ C.subtype ∘ₗ c.toLinearMap))
  have hf : ∀ w : NilModel F k m,
      f w = (c w.1 : V) + ((((d w.2.1 : D) : LinearMap.ker N) : V) + N (c w.2.2)) := by
    intro w
    simp [f]
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    rw [← LinearMap.comp_apply, hN, LinearMap.zero_apply]
  have hNf : ∀ w, N (f w) = N (c w.1) := by
    intro w
    rw [hf, map_add, map_add, hNN, add_zero, ((d w.2.1 : D) : LinearMap.ker N).2, add_zero]
  have hCK : ∀ x, N (c x : V) = 0 → x = 0 := by
    intro x hx
    have h1 : (c x : V) = 0 := Submodule.disjoint_def.1 hC.disjoint _ hx (c x).2
    have h2 : c x = 0 := Subtype.ext h1
    exact (LinearEquiv.map_eq_zero_iff c).1 h2
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, z, y⟩ h
    have hx : x = 0 := hCK x (by rw [← hNf (x, z, y), h, map_zero])
    subst hx
    rw [hf] at h
    simp only [map_zero, ZeroMemClass.coe_zero, zero_add] at h
    set u : LinearMap.ker N := ((d z : D) : LinearMap.ker N) with hu
    set w : LinearMap.ker N := ⟨N (c y), hIK ⟨c y, rfl⟩⟩ with hw
    have huw : u + w = 0 := Subtype.ext h
    have hwI : w ∈ I' := ⟨c y, rfl⟩
    have huI : u ∈ I' := by
      rw [eq_neg_of_add_eq_zero_left huw]
      exact I'.neg_mem hwI
    have hu0 : u = 0 := Submodule.disjoint_def.1 hD.disjoint _ huI (d z).2
    have hdz : d z = 0 := Subtype.ext hu0
    have hz : z = 0 := (LinearEquiv.map_eq_zero_iff d).1 hdz
    subst hz
    have hw0 : w = 0 := by rw [← huw, hu0, zero_add]
    have hy : y = 0 := hCK y (congrArg Subtype.val hw0)
    subst hy
    rfl
  refine ⟨LinearMap.linearEquivOfInjective f hinj ?_, fun w => ?_⟩
  · simp only [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  · simp only [LinearMap.linearEquivOfInjective_apply, nilModelMap_apply]
    rw [hNf, hf]
    simp

end CFSG.LargeExtraspecial.GLR
