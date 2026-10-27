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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Polynomial

section Generic

theorem exists_pow_pow_eq {M : Type*} [Monoid M] {a : M} {p m : ℕ} (hp : p.Prime)
    (hap : a ^ p = 1) (hm : ¬ p ∣ m) : ∃ k : ℕ, (a ^ m) ^ k = a := by
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun h0 => hm ((ZMod.natCast_eq_zero_iff m p).1 h0)
  refine ⟨((m : ZMod p)⁻¹).val, ?_⟩
  rw [← pow_mul, pow_eq_pow_mod _ hap]
  have h1 : ((m * ((m : ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_inv_cancel₀ hm0]
  have h2 : m * ((m : ZMod p)⁻¹).val % p = 1 := by
    rw [← ZMod.val_natCast, h1, ZMod.val_one]
  rw [h2, pow_one]

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [Ring R] {E : R} (hE : E * E = 0)
    (m : ℕ) : (1 + E) ^ m = 1 + (m : R) * E := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    calc (1 + (m : R) * E) * (1 + E) = 1 + (m : R) * E + E + (m : R) * (E * E) := by
          noncomm_ring
      _ = 1 + ((m : R) + 1) * E := by rw [hE, mul_zero, add_zero]; noncomm_ring

theorem eq_one_of_pow_eq_one_of_sq {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n K} {p : ℕ} (hp : (p : K) ≠ 0) (hDp : D ^ p = 1)
    (hD : (D - 1) * (D - 1) = 0) : D = 1 := by
  have h1 := one_add_pow_of_mul_self_eq_zero hD p
  rw [add_sub_cancel, hDp] at h1
  have h2 : p • (D - 1) = 0 := by
    rw [nsmul_eq_mul]
    have := congrArg (· - 1) h1
    simpa using this.symm
  rw [← Nat.cast_smul_eq_nsmul K, smul_eq_zero] at h2
  exact sub_eq_zero.1 (h2.resolve_left hp)

theorem prod_X_sub_C_dvd {K : Type*} [Field K] (s : Finset K) {P : K[X]} (hP : P ≠ 0)
    (hs : ∀ a ∈ s, P.IsRoot a) : ∏ a ∈ s, (X - C a) ∣ P := by
  have hle : s.val ≤ P.roots :=
    (Multiset.le_iff_subset s.nodup).2 fun a ha => (mem_roots hP).2 (hs a ha)
  calc ∏ a ∈ s, (X - C a) = (s.val.map fun a => X - C a).prod := rfl
    _ ∣ (P.roots.map fun a => X - C a).prod :=
      Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
    _ ∣ P := prod_multiset_X_sub_C_dvd P

theorem prod_X_sub_C_univ (K : Type*) [Field K] [Fintype K] :
    ∏ a : K, (X - C a) = X ^ Fintype.card K - X := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hmon : (X ^ Fintype.card K - X : K[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hroots := FiniteField.roots_X_pow_card_sub_X K
  have hcard : Multiset.card (X ^ Fintype.card K - X : K[X]).roots =
      (X ^ Fintype.card K - X : K[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq K h1]
    rfl
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard, hroots]
  rfl

theorem exists_det_eq_zero {K : Type*} [Field K] [Fintype K] {n : ℕ}
    {T : Matrix (Fin n) (Fin n) K} {N : ℕ} (hN : 1 < N) (hT : T ^ Fintype.card K = T)
    (hTN : T ^ N ≠ T) : ∃ β : K, β ^ N ≠ β ∧ (T - algebraMap K _ β).det = 0 := by
  classical
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter fun β : K => β ^ N ≠ β with hS
  set S' := Finset.univ.filter fun β : K => ¬ β ^ N ≠ β with hS'
  have hsplit : (∏ β ∈ S, (X - C β)) * ∏ β ∈ S', (X - C β) = X ^ Fintype.card K - X := by
    rw [Finset.prod_filter_mul_prod_filter_not, prod_X_sub_C_univ]
  have hev := congrArg (aeval T) hsplit
  rw [map_mul, map_sub, map_pow, aeval_X, hT, sub_self] at hev
  have hdetS : (aeval T (∏ β ∈ S, (X - C β))).det ≠ 0 := by
    have e : ∀ s : Finset K, (aeval T (∏ β ∈ s, (X - C β))).det =
        ∏ β ∈ s, (T - algebraMap K _ β).det := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, det_mul, ih, map_sub,
          aeval_X, aeval_C]
    rw [e]
    exact Finset.prod_ne_zero_iff.2 fun β hβ => hne β (Finset.mem_filter.1 hβ).2
  have hunit : IsUnit (aeval T (∏ β ∈ S, (X - C β))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdetS)
  have hS0 : aeval T (∏ β ∈ S', (X - C β)) = 0 := hunit.mul_right_eq_zero.1 hev
  obtain ⟨R, hR⟩ := prod_X_sub_C_dvd S' (FiniteField.X_pow_card_sub_X_ne_zero K hN)
    fun β hβ => by
      have hβ' : β ^ N = β := by simpa [hS'] using hβ
      simp [IsRoot, hβ']
  apply hTN
  have e := congrArg (aeval T) hR
  rwa [map_mul, hS0, zero_mul, map_sub, map_pow, aeval_X, sub_eq_zero] at e

end Generic

end CFSG.OddStandard.GH71.S55.C5U
