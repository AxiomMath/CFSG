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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Equiv

def sigma0 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem orderOf_sigma0 : orderOf sigma0 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_ <;> decide +kernel

theorem card_normalizer_sigma0_le :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers sigma0 : Subgroup (alternatingGroup (Fin 6))) :
      Set (alternatingGroup (Fin 6)))) ≤ 10 := by
  classical
  let T : Finset (alternatingGroup (Fin 6)) := Finset.univ.filter fun τ =>
    τ * sigma0 * τ⁻¹ = sigma0 ∨ τ * sigma0 * τ⁻¹ = sigma0 ^ 2 ∨ τ * sigma0 * τ⁻¹ = sigma0 ^ 3 ∨
      τ * sigma0 * τ⁻¹ = sigma0 ^ 4
  have hT : T.card ≤ 10 := by decide +kernel
  have hsub : ∀ τ : Subgroup.normalizer ((Subgroup.zpowers sigma0 : Subgroup
      (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))), (τ : alternatingGroup (Fin 6)) ∈ T := by
    intro τ
    have hmem : (τ : alternatingGroup (Fin 6)) * sigma0 * (τ : alternatingGroup (Fin 6))⁻¹ ∈
        Subgroup.zpowers sigma0 :=
      (Subgroup.mem_normalizer_iff.mp τ.2 sigma0).mp (Subgroup.mem_zpowers sigma0)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h5 : sigma0 ^ (5 : ℤ) = 1 := by
      rw [zpow_ofNat]; exact pow_orderOf_eq_one sigma0 ▸ by rw [orderOf_sigma0]
    have hmod : sigma0 ^ j = sigma0 ^ (j % 5) := zpow_eq_zpow_emod j h5
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hj, hmod]
    have hr : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
    rcases hr with h | h | h | h | h <;> rw [h]
    ·
      exfalso
      have : (τ : alternatingGroup (Fin 6)) * sigma0 * (τ : alternatingGroup (Fin 6))⁻¹ = 1 := by
        rw [← hj, hmod, h, zpow_zero]
      have h1 : sigma0 = 1 := by
        have := congrArg (fun y => (τ : alternatingGroup (Fin 6))⁻¹ * y * (τ : alternatingGroup (Fin 6))) this
        simpa [mul_assoc] using this
      have : orderOf sigma0 = 1 := by rw [h1]; exact orderOf_one
      rw [orderOf_sigma0] at this
      omega
    all_goals simp
  calc Nat.card (Subgroup.normalizer ((Subgroup.zpowers sigma0 : Subgroup
        (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))))
      ≤ T.card := by
        classical
        rw [Nat.card_eq_fintype_card]
        have hinj : Function.Injective (fun τ : Subgroup.normalizer ((Subgroup.zpowers sigma0 :
            Subgroup (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))) =>
            (⟨(τ : alternatingGroup (Fin 6)), hsub τ⟩ : T)) := fun a b h =>
          Subtype.ext (congrArg (fun y : T => (y : alternatingGroup (Fin 6))) h)
        have := Fintype.card_le_of_injective _ hinj
        simpa using this
    _ ≤ 10 := hT


theorem card_alt_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

abbrev nz (σ : alternatingGroup (Fin 6)) : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup (alternatingGroup (Fin 6))) :
    Set (alternatingGroup (Fin 6)))

theorem normalizer_index_zpowers (σ : alternatingGroup (Fin 6)) (hσ : orderOf σ = 5) :
    Nat.card (Sylow 5 (alternatingGroup (Fin 6))) = (nz σ).index ∧
      Nat.card (nz σ) * (nz σ).index = 360 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (Subgroup.zpowers σ) = 5 := by rw [Nat.card_zpowers, hσ]
  have hP : IsPGroup 5 (Subgroup.zpowers σ) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hidx : (Subgroup.zpowers σ).index = 72 := by
    have := (Subgroup.zpowers σ).card_mul_index
    rw [hcard, card_alt_six'] at this
    omega
  have hnd : ¬ 5 ∣ (Subgroup.zpowers σ).index := by rw [hidx]; norm_num
  let S : Sylow 5 (alternatingGroup (Fin 6)) := hP.toSylow hnd
  have hS : (S : Subgroup (alternatingGroup (Fin 6))) = Subgroup.zpowers σ :=
    IsPGroup.toSylow_coe hP hnd
  refine ⟨?_, ?_⟩
  · have h := S.card_eq_index_normalizer
    have hS' : (S : Set (alternatingGroup (Fin 6))) =
        ((Subgroup.zpowers σ : Subgroup (alternatingGroup (Fin 6))) :
          Set (alternatingGroup (Fin 6))) := by rw [← hS]; rfl
    rw [hS'] at h
    exact h
  · have := (nz σ).card_mul_index
    rwa [card_alt_six'] at this

theorem card_normalizer_zpowers_le_ten (σ : alternatingGroup (Fin 6)) (hσ : orderOf σ = 5) :
    Nat.card (nz σ) ≤ 10 := by
  obtain ⟨h1, h2⟩ := normalizer_index_zpowers σ hσ
  obtain ⟨h1', h2'⟩ := normalizer_index_zpowers sigma0 orderOf_sigma0
  have hN0 : Nat.card (nz sigma0) ≤ 10 := card_normalizer_sigma0_le
  have hn : 36 ≤ Nat.card (Sylow 5 (alternatingGroup (Fin 6))) := by
    rw [h1']
    by_contra hlt
    push Not at hlt
    nlinarith
  rw [h1] at hn
  nlinarith

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
