module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

private theorem exists_conj_le_of_card_eq {C A B : Subgroup X} (hAC : A ≤ C)
    (hAcard : Nat.card A = 2 ^ (Nat.card C).factorization 2) (hBC : B ≤ C)
    (hB2 : IsPGroup 2 B) : ∃ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ : Nat.card (A.subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hAcard]
  have hB₁ : IsPGroup 2 (B.subgroupOf C) := hB2.of_equiv (subgroupOfEquivOfLe hBC).symm
  obtain ⟨T, hT⟩ := hB₁.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq C T (Sylow.ofCard _ hS₁)
  refine ⟨h, h.2, fun b hb => ?_⟩
  have key : ((h • T : Sylow 2 C) : Subgroup C) = A.subgroupOf C := by
    rw [hh, Sylow.coe_ofCard]
  rw [Sylow.coe_subgroup_smul] at key
  have h1 : MulAut.conj h • (⟨b, hBC hb⟩ : C) ∈ MulAut.conj h • (T : Subgroup C) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (show (⟨b, hBC hb⟩ : C) ∈ B.subgroupOf C from hb))
  rw [key] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply, mem_subgroupOf] using h1

private theorem disjoint_of_odd {A N : Subgroup X} {k : ℕ} (hk : Nat.card A = 2 ^ k)
    (hN : Odd (Nat.card N)) : Disjoint N A := by
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [hk]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hN)

private theorem card_eq_two_pow_of_odd {A N : Subgroup X} {k : ℕ} (hk : Nat.card A = 2 ^ k)
    (hN : Odd (Nat.card N)) (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card A = 2 ^ (Nat.card (A ⊔ N : Subgroup X)).factorization 2 := by
  have hcard : Nat.card (A ⊔ N : Subgroup X) = Nat.card N * Nat.card A := by
    rw [sup_comm]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N A hAN
      (disjoint_of_odd hk hN)
  rw [hcard, hk, Nat.factorization_mul Nat.card_pos.ne' (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hN.not_two_dvd_nat,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

private theorem conj_mem_of_mem_normalizer {N : Subgroup X} {g n : X}
    (hg : g ∈ normalizer (N : Set X)) (hn : n ∈ N) : g * n * g⁻¹ ∈ N :=
  (mem_set_normalizer_iff.mp hg n).mp hn

theorem exists_mul_normalizes_of_odd {A N : Subgroup X} (hA : IsPGroup 2 A)
    (hN : Odd (Nat.card N)) (hAN : A ≤ normalizer (N : Set X)) {y : X}
    (hyN : y ∈ normalizer (N : Set X)) (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A ⊔ N) :
    ∃ n ∈ N, (∀ a ∈ A, (y * n) * a * (y * n)⁻¹ ∈ A) ∧
      ∀ a ∈ A, ∀ a' ∈ A, a'⁻¹ * (y * a * y⁻¹) ∈ N → (y * n) * a * (y * n)⁻¹ = a' := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA
  have hBC : A.map (MulAut.conj y).toMonoidHom ≤ A ⊔ N := by
    rintro _ ⟨a, ha, rfl⟩
    exact hyA a ha
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_card_eq le_sup_left (card_eq_two_pow_of_odd hk hN hAN)
    hBC (hA.map _)
  obtain ⟨a₀, ha₀, n₀, hn₀, rfl⟩ : ∃ a₀ ∈ A, ∃ n₀ ∈ N, a₀ * n₀ = c := by
    refine Set.mem_mul.mp ?_
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A N hAN]
    exact hcC
  have hc' : ∀ a ∈ A, a₀ * n₀ * (y * a * y⁻¹) * (a₀ * n₀)⁻¹ ∈ A := fun a ha =>
    hc _ (Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩)
  obtain ⟨n, hn, hyn⟩ : ∃ n ∈ N, y * n = n₀ * y :=
    ⟨y⁻¹ * n₀ * y, by simpa using conj_mem_of_mem_normalizer (inv_mem hyN) hn₀, by group⟩
  have hfirst : ∀ a ∈ A, (y * n) * a * (y * n)⁻¹ ∈ A := by
    intro a ha
    have e : (y * n) * a * (y * n)⁻¹ = a₀⁻¹ * (a₀ * n₀ * (y * a * y⁻¹) * (a₀ * n₀)⁻¹) * a₀ := by
      rw [hyn]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem ha₀) (hc' a ha)) ha₀
  refine ⟨n, hn, hfirst, fun a ha a' ha' hm => ?_⟩
  have hmemN : a'⁻¹ * ((y * n) * a * (y * n)⁻¹) ∈ N := by
    have e : a'⁻¹ * ((y * n) * a * (y * n)⁻¹) =
        (a'⁻¹ * n₀ * a') * (a'⁻¹ * (y * a * y⁻¹)) * n₀⁻¹ := by
      rw [hyn]
      group
    rw [e]
    refine mul_mem (mul_mem ?_ hm) (inv_mem hn₀)
    simpa using conj_mem_of_mem_normalizer (hAN (inv_mem ha')) hn₀
  have h1 := Subgroup.disjoint_def.mp (disjoint_of_odd hk hN) hmemN
    (mul_mem (inv_mem ha') (hfirst a ha))
  exact (inv_mul_eq_one.mp h1).symm

end CFSG.ComponentClassification.SolMax.Sig36.E32
