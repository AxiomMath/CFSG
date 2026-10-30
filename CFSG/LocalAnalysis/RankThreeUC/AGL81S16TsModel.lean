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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankThreeUC

private theorem two_finrank_le_of_isotropic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (W : Submodule K V) (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hB x
    intro y
    simpa using LinearMap.congr_fun hx y
  have hdimV : Module.finrank K V = Module.finrank K (V →ₗ[K] K) :=
    Subspace.dual_finrank_eq.symm
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimV).mp hinj
  set R : V →ₗ[K] W →ₗ[K] K := B.compl₂ W.subtype
  have hRapp : ∀ (x : V) (w : W), R x w = B x (w : V) := fun x w => rfl
  have hRsurj : Function.Surjective R := by
    intro f
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    obtain ⟨x, hx⟩ := hsurj g
    refine ⟨x, LinearMap.ext fun w => ?_⟩
    rw [hRapp, hx]
    simpa using LinearMap.congr_fun hg w
  have hrank := LinearMap.finrank_range_add_finrank_ker R
  have hdimW : Module.finrank K (W →ₗ[K] K) = Module.finrank K W := Subspace.dual_finrank_eq
  rw [LinearMap.range_eq_top.mpr hRsurj, finrank_top, hdimW] at hrank
  have hle : W ≤ LinearMap.ker R := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    rw [hRapp, LinearMap.zero_apply]
    exact hW x hx w.1 w.2
  have hmono := Submodule.finrank_mono hle
  omega

theorem totally_singular_card_le {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (S : AddSubgroup (Fin 4 → F))
    (hS : ∀ x ∈ S, x ≠ 0 → ∑ i, x i ^ (2 ^ n + 1) = 0) : Nat.card S ≤ 2 ^ (4 * n) := by
  letI : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, hF]
    ring
  have hchar : ringChar F = 2 :=
    FiniteField.even_card_iff_char_two.mpr (by
      rw [hFcard]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega)))
  haveI : CharP F 2 := by
    rw [← hchar]
    infer_instance
  letI : Algebra (ZMod 2) F := (ZMod.castHom (dvd_refl 2) F).toAlgebra
  haveI : Module.Finite (ZMod 2) F := Module.finite_iff_finite.mpr inferInstance
  have hZ2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hfrF : Module.finrank (ZMod 2) F = 2 * n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hZ2, hF] at h1
    have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by ring
    rw [h2] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hfrV : Module.finrank (ZMod 2) (Fin 4 → F) = 8 * n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 4 → F)
    rw [Nat.card_fun, hF, hZ2, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h1
    have h2 : ((2 ^ n) ^ 2) ^ 4 = 2 ^ (8 * n) := by ring
    rw [h2] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hsq : 2 ^ n * 2 ^ n = Fintype.card F := by
    rw [hFcard, ← pow_add, two_mul]
  have hpow2 : ∀ a : F, a ^ (2 ^ n * 2 ^ n) = a := fun a => by
    rw [hsq]
    exact FiniteField.pow_card a
  have hsing : ∀ z ∈ S, ∑ i, z i ^ (2 ^ n) * z i = 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · simpa only [pow_succ] using hS z hz hz0
  have hsymm : ∀ x y : Fin 4 → F,
      (∑ i, x i ^ (2 ^ n) * y i) ^ (2 ^ n) = ∑ i, y i ^ (2 ^ n) * x i := by
    intro x y
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, hpow2]
    ring
  have hadd_left : ∀ x x' y : Fin 4 → F,
      ∑ i, (x + x') i ^ (2 ^ n) * y i
        = ∑ i, x i ^ (2 ^ n) * y i + ∑ i, x' i ^ (2 ^ n) * y i := by
    intro x x' y
    simp only [Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]
  have hadd_right : ∀ x y y' : Fin 4 → F,
      ∑ i, x i ^ (2 ^ n) * (y + y') i
        = ∑ i, x i ^ (2 ^ n) * y i + ∑ i, x i ^ (2 ^ n) * y' i := by
    intro x y y'
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hcross : ∀ x ∈ S, ∀ y ∈ S,
      (∑ i, x i ^ (2 ^ n) * y i) + ∑ i, y i ^ (2 ^ n) * x i = 0 := by
    intro x hx y hy
    have hxy := hsing (x + y) (S.add_mem hx hy)
    have e : ∑ i, (x + y) i ^ (2 ^ n) * (x + y) i
        = ∑ i, x i ^ (2 ^ n) * x i + ((∑ i, x i ^ (2 ^ n) * y i) + ∑ i, y i ^ (2 ^ n) * x i)
          + ∑ i, y i ^ (2 ^ n) * y i := by
      simp only [Pi.add_apply, add_pow_char_pow, add_mul, mul_add, Finset.sum_add_distrib]
      ring
    rw [e, hsing x hx, hsing y hy] at hxy
    linear_combination hxy
  have htr_zero : ∀ c : F, c ^ (2 ^ n) = c → Algebra.trace (ZMod 2) F c = 0 := by
    intro c hc
    have key := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) F c
    rw [hZ2, hfrF] at key
    have hshift : ∀ i : ℕ, c ^ (2 ^ (n + i)) = c ^ (2 ^ i) := by
      intro i
      rw [pow_add, pow_mul, hc]
    have hsum : ∑ i ∈ Finset.range (2 * n), c ^ (2 ^ i) = 0 := by
      rw [two_mul, Finset.sum_range_add]
      simp only [hshift]
      rw [← two_mul, (CharTwo.two_eq_zero : (2 : F) = 0), zero_mul]
    apply (algebraMap (ZMod 2) F).injective
    rw [key, hsum, map_zero]
  obtain ⟨d₀, hd₀⟩ : ∃ d : F, Algebra.trace (ZMod 2) F d = 1 :=
    Algebra.trace_surjective (K := ZMod 2) (L := F) 1
  have hZ2cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let B : (Fin 4 → F) →ₗ[ZMod 2] (Fin 4 → F) →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) F (∑ i, x i ^ (2 ^ n) * y i))
      (fun x x' y => by simp only [hadd_left, map_add])
      (fun c x y => by rcases hZ2cases c with rfl | rfl <;> simp)
      (fun x y y' => by simp only [hadd_right, map_add])
      (fun c x y => by rcases hZ2cases c with rfl | rfl <;> simp)
  have hB_apply : ∀ x y : Fin 4 → F,
      B x y = Algebra.trace (ZMod 2) F (∑ i, x i ^ (2 ^ n) * y i) := fun x y => rfl
  have hBnd : ∀ x : Fin 4 → F, (∀ y, B x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    have ha : x i ^ (2 ^ n) ≠ 0 := pow_ne_zero _ hi
    have hy := hx (Pi.single i ((x i ^ (2 ^ n))⁻¹ * d₀) : Fin 4 → F)
    rw [hB_apply] at hy
    have hsum : ∑ j, x j ^ (2 ^ n) * (Pi.single i ((x i ^ (2 ^ n))⁻¹ * d₀) : Fin 4 → F) j = d₀ := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_inv_cancel_left₀ ha]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum, hd₀] at hy
    exact one_ne_zero hy
  let W : Submodule (ZMod 2) (Fin 4 → F) := AddSubgroup.toZModSubmodule 2 S
  have hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
    intro x hx y hy
    have hx' : x ∈ S := hx
    have hy' : y ∈ S := hy
    rw [hB_apply]
    apply htr_zero
    have h1 := hcross x hx' y hy'
    rw [← hsymm x y] at h1
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h1 - (∑ i, x i ^ (2 ^ n) * y i) * h2
  have hlin := two_finrank_le_of_isotropic B hBnd W hW
  have hcardS : Nat.card S = 2 ^ Module.finrank (ZMod 2) W := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hZ2] at h1
    rw [← h1]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hWle : Module.finrank (ZMod 2) W ≤ 4 * n := by omega
  rw [hcardS]
  exact Nat.pow_le_pow_right (by norm_num) hWle

end CFSG.LocalAnalysis.RankThreeUC
