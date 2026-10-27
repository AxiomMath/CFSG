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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
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

namespace CFSG.LocalAnalysis.RankThreeUC

@[expose] def sesqPerp {K : Type*} [Field K] (σ : K ≃+* K) {n : ℕ}
    (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {x | ∀ w ∈ W, ∑ i, σ (w i) * x i = 0}
  add_mem' := by
    intro x y hx hy w hw
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx w hw, hy w hw, add_zero]
  zero_mem' := by
    intro w _
    simp
  smul_mem' := by
    intro c x hx w hw
    have h : ∑ i, σ (w i) * x i = 0 := hx w hw
    have h' : ∑ i, σ (w i) * (c • x) i = c * ∑ i, σ (w i) * x i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h', h, mul_zero]

theorem card_sesqPerp_mul_card {K : Type*} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    Nat.card ↥(sesqPerp σ W) * Nat.card ↥W = Nat.card K ^ n := by
  let G : (Fin n → K) →+ Module.Dual K W :=
    { toFun := fun x =>
        { toFun := fun w => ∑ i, (w : Fin n → K) i * σ.symm (x i)
          map_add' := fun w₁ w₂ => by
            simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
          map_smul' := fun c w => by
            simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
              Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring }
      map_zero' := LinearMap.ext fun w => by simp
      map_add' := fun x₁ x₂ => LinearMap.ext fun w => by
        simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, map_add,
          mul_add, Finset.sum_add_distrib] }
  have hGapp : ∀ (x : Fin n → K) (w : W), G x w = ∑ i, (w : Fin n → K) i * σ.symm (x i) :=
    fun _ _ => rfl
  have hkey : ∀ (w x : Fin n → K), ∑ i, w i * σ.symm (x i) = 0 ↔ ∑ i, σ (w i) * x i = 0 := by
    intro w x
    constructor
    · intro h
      have h' : σ (∑ i, w i * σ.symm (x i)) = σ 0 := by rw [h]
      simpa [map_sum, map_mul] using h'
    · intro h
      have h' : σ.symm (∑ i, σ (w i) * x i) = σ.symm 0 := by rw [h]
      simpa [map_sum, map_mul] using h'
  have hker : ∀ x : Fin n → K, x ∈ G.ker ↔ x ∈ sesqPerp σ W := by
    intro x
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro hx w hw
      have h : G x ⟨w, hw⟩ = 0 := by simp [hx]
      rw [hGapp] at h
      exact (hkey w x).mp h
    · intro hx
      apply LinearMap.ext
      rintro ⟨w, hw⟩
      rw [hGapp, LinearMap.zero_apply]
      exact (hkey w x).mpr (hx w hw)
  have hsurj : Function.Surjective G := by
    intro f
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    refine ⟨fun i => σ (g fun j => if i = j then 1 else 0), ?_⟩
    apply LinearMap.ext
    rintro ⟨w, hw⟩
    have hfw : f ⟨w, hw⟩ = g w := (LinearMap.congr_fun hg ⟨w, hw⟩).symm
    rw [hGapp, hfw, LinearMap.pi_apply_eq_sum_univ g w]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RingEquiv.symm_apply_apply, smul_eq_mul]
  have hcardKer : Nat.card G.ker * Nat.card (Module.Dual K W) = Nat.card (Fin n → K) :=
    AddSubgroup.card_ker_mul_card_of_surjective hsurj
  have hKerCard : Nat.card ↥(sesqPerp σ W) = Nat.card G.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hker x).symm)
  have hDual : Nat.card (Module.Dual K W) = Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K W), Subspace.dual_finrank_eq,
      Module.natCard_eq_pow_finrank (K := K) (V := W)]
  have hFin : Nat.card (Fin n → K) = Nat.card K ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Fin n → K), Module.finrank_fin_fun]
  rw [hKerCard, ← hDual, hcardKer, hFin]

theorem natCard_linearMap {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [AddCommGroup W] [Module K W] [Module.Finite K W] :
    Nat.card (V →ₗ[K] W) = Nat.card K ^ (Module.finrank K V * Module.finrank K W) := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := V →ₗ[K] W), Module.finrank_linearMap]

theorem card_linearMaps_vanishing_into {K N : Type*} [Field K] [Finite K] [AddCommGroup N]
    [Module K N] [Module.Finite K N] (C I : Submodule K N) :
    Nat.card {φ : N →ₗ[K] N // (∀ x ∈ C, φ x = 0) ∧ ∀ x, φ x ∈ I} =
      Nat.card K ^ ((Module.finrank K N - Module.finrank K C) * Module.finrank K I) := by
  have hquot : Module.finrank K (N ⧸ C) = Module.finrank K N - Module.finrank K C := by
    have h := C.finrank_quotient_add_finrank
    omega
  let e : {φ : N →ₗ[K] N // (∀ x ∈ C, φ x = 0) ∧ ∀ x, φ x ∈ I} ≃ ((N ⧸ C) →ₗ[K] I) :=
    { toFun := fun φ => C.liftQ (LinearMap.codRestrict I φ.1 φ.2.2) (by
        intro x hx
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        simp [φ.2.1 x hx])
      invFun := fun f => ⟨I.subtype ∘ₗ f ∘ₗ C.mkQ, by
          intro x hx
          have h0 : C.mkQ x = 0 := by simpa using hx
          simp [h0], fun x => (f (C.mkQ x)).2⟩
      left_inv := fun φ => by
        apply Subtype.ext
        apply LinearMap.ext
        intro x
        simp
      right_inv := fun f => by
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := C.mkQ_surjective q
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, natCard_linearMap, hquot]

end CFSG.LocalAnalysis.RankThreeUC
