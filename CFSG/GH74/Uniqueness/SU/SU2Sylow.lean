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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

theorem exists_sylow_le_of_odd_index {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hodd : Odd H.index) : ∃ S : Sylow 2 X, (S : Subgroup X) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hcard : Nat.card ↥((P₀ : Subgroup H).map H.subtype) =
      2 ^ (Nat.card X).factorization 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, P₀.card_eq_multiplicity]
    congr 1
    have h1 : Nat.card X = H.index * Nat.card H := (Subgroup.index_mul_card H).symm
    have hne1 : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hne2 : Nat.card H ≠ 0 := Nat.card_pos.ne'
    rw [h1, Nat.factorization_mul hne1 hne2]
    have : ¬ 2 ∣ H.index := by
      rw [Nat.odd_iff] at hodd
      omega
    simp [Nat.factorization_eq_zero_of_not_dvd this]
  exact ⟨Sylow.ofCard _ hcard, Subgroup.map_subtype_le _⟩

theorem le_of_odd_card_of_index_pow {X : Type*} [Group X] [Finite X] {K Y : Subgroup X}
    [K.Normal] (hY : Odd (Nat.card Y)) {a : ℕ} (hK : K.index = 2 ^ a) : Y ≤ K := by
  intro y hy
  have h1 : orderOf (QuotientGroup.mk y : X ⧸ K) ∣ 2 ^ a := by
    rw [← hK, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (QuotientGroup.mk y : X ⧸ K) ∣ Nat.card Y :=
    (orderOf_map_dvd (QuotientGroup.mk' K) y).trans (Subgroup.orderOf_dvd_natCard Y hy)
  have hcop : Nat.Coprime (2 ^ a) (Nat.card Y) := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [Nat.odd_iff] at hY
    omega
  have h3 : orderOf (QuotientGroup.mk y : X ⧸ K) ∣ Nat.gcd (2 ^ a) (Nat.card Y) :=
    Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  have h4 : (QuotientGroup.mk y : X ⧸ K) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact (QuotientGroup.eq_one_iff y).1 h4

theorem exists_mem_of_normal_index_pow {X α : Type*} [Group X] [Finite X] [MulAction X α]
    {K : Subgroup X} [K.Normal] {a : ℕ} (hK : K.index = 2 ^ a) (v : α)
    (hodd : Odd (MulAction.orbit X v).ncard) (x : X) : ∃ k ∈ K, x • v = k • v := by
  set Xv := MulAction.stabilizer X v with hXv
  have hrel := Subgroup.relIndex_mul_index (le_sup_right : Xv ≤ K ⊔ Xv)
  have hindex : Xv.index = (MulAction.orbit X v).ncard := MulAction.index_stabilizer X v
  have hdvd1 : (K ⊔ Xv).index ∣ 2 ^ a := hK ▸ Subgroup.index_dvd_of_le le_sup_left
  have hdvd2 : (K ⊔ Xv).index ∣ (MulAction.orbit X v).ncard := by
    rw [← hindex, ← hrel]
    exact Dvd.intro_left _ rfl
  have hodd2 : Odd (K ⊔ Xv).index := hodd.of_dvd_nat hdvd2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd2
    exact (Nat.not_even_iff_odd.2 hodd2) (Nat.even_pow.2 ⟨even_two, hne⟩)
  have htop : K ⊔ Xv = ⊤ := Subgroup.index_eq_one.1 (by rw [hi, hi0, pow_zero])
  have hx : x ∈ ((K ⊔ Xv : Subgroup X) : Set X) := by rw [htop]; trivial
  rw [Subgroup.normal_mul] at hx
  obtain ⟨k, hk, xv, hxv, rfl⟩ := hx
  refine ⟨k, hk, ?_⟩
  rw [mul_smul, MulAction.mem_stabilizer_iff.1 hxv]

end CFSG.GH74.Uniqueness.SU.SU2
