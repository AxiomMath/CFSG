module

import CFSG.FeitThompson.OddOrderTheorem
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
public import Mathlib.GroupTheory.IsPerfect
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Pointwise

namespace CFSG.ClassicalInvolution.Asc77.ExactD

variable {G : Type} [Group G]

theorem mem_of_sq_mem_of_odd {K : Subgroup G} {n : G} (hn : Odd (orderOf n))
    (h : n * n ∈ K) : n ∈ K := by
  obtain ⟨k, hk⟩ := hn
  have h1 : n ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one n
  have h2 : n = (n * n) ^ (k + 1) := by
    calc n = n ^ (2 * k + 1) * n := by rw [h1, one_mul]
      _ = (n * n) ^ (k + 1) := by
        rw [← pow_succ, ← sq, ← pow_mul]
        congr 1
  rw [h2]
  exact pow_mem h (k + 1)

theorem mem_of_involution_mem_sup_odd [Finite G] {K N : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hNK : N ≤ Subgroup.normalizer (K : Set G))
    (hodd : Odd (Nat.card N)) {u : G} (hu : u ∈ K ⊔ N) (hu2 : u * u = 1) : u ∈ K := by
  have hset : ((K ⊔ N : Subgroup G) : Set G) = (K : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K N hKN
  have hu' : u ∈ (K : Set G) * (N : Set G) := hset ▸ hu
  obtain ⟨k, hk, n, hn, rfl⟩ := hu'
  have hc : n * k * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hNK hn) k).mp hk
  have h1 : (k * (n * k * n⁻¹)) * (n * n) = 1 := by
    calc (k * (n * k * n⁻¹)) * (n * n) = k * n * (k * n) := by group
      _ = 1 := hu2
  have h2 : n * n = (k * (n * k * n⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hnn : n * n ∈ K := h2 ▸ K.inv_mem (K.mul_mem hk hc)
  have hn' : Odd (orderOf n) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
  exact K.mul_mem hk (mem_of_sq_mem_of_odd hn' hnn)

theorem conj_mem_inf_centralizer {M N : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) {m c : G} (hm : m ∈ M)
    (hc : c ∈ M ⊓ Subgroup.centralizer (N : Set G)) :
    m * c * m⁻¹ ∈ M ⊓ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_inf] at hc ⊢
  obtain ⟨hcM, hcN⟩ := hc
  refine ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hn' : m⁻¹ * n * m ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN (M.inv_mem hm)) n).mp hn
    simpa using this
  have h1 : (m⁻¹ * n * m) * c = c * (m⁻¹ * n * m) := Subgroup.mem_centralizer_iff.mp hcN _ hn'
  calc n * (m * c * m⁻¹) = m * ((m⁻¹ * n * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * n * m)) * m⁻¹ := by rw [h1]
    _ = (m * c * m⁻¹) * n := by group

theorem le_normalizer_inf_centralizer {M N : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_inf_centralizer hMN hm hc, fun hc => ?_⟩
  have := conj_mem_inf_centralizer hMN (M.inv_mem hm) hc
  simpa [mul_assoc] using this

theorem le_centralizer_of_perfect_of_cover [Finite G] {M N : Subgroup G} (hperf : ⁅M, M⁆ = M)
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N))
    (hcov : M ≤ (M ⊓ Subgroup.centralizer (N : Set G)) ⊔ N) :
    M ≤ Subgroup.centralizer (N : Set G) := by
  classical
  set C : Subgroup G := M ⊓ Subgroup.centralizer (N : Set G) with hC
  have hCM : C ≤ M := inf_le_left
  have hCnorm : (C.subgroupOf M).Normal := by
    refine ⟨fun c hc m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    exact conj_mem_inf_centralizer hMN m.2 hc
  have hperfM : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hperf
  have hsolvN : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let φ : ↥N →* (↥M ⧸ C.subgroupOf M) :=
    (QuotientGroup.mk' (C.subgroupOf M)).comp (Subgroup.inclusion hNM)
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf M) q
    have hset : ((C ⊔ N : Subgroup G) : Set G) = (C : Set G) * (N : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right C N (hCM.trans hMN)
    have hm : (m : G) ∈ (C : Set G) * (N : Set G) := hset ▸ hcov m.2
    obtain ⟨c, hc, n, hn, hcn⟩ := hm
    have hc' : c ∈ C := hc
    refine ⟨⟨n, hn⟩, ?_⟩
    have hmeq : m = ⟨c, hCM hc'⟩ * ⟨n, hNM hn⟩ := Subtype.ext hcn.symm
    have hcmem : (⟨c, hCM hc'⟩ : ↥M) ∈ C.subgroupOf M := Subgroup.mem_subgroupOf.mpr hc'
    show QuotientGroup.mk' (C.subgroupOf M) ⟨n, hNM hn⟩ = QuotientGroup.mk' (C.subgroupOf M) m
    have h1 : QuotientGroup.mk' (C.subgroupOf M) ⟨c, hCM hc'⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hcmem
    rw [hmeq, map_mul, h1, one_mul]
  have hsolvQ : Group.IsSolvable (↥M ⧸ C.subgroupOf M) := Group.isSolvable_of_surjective hsurj
  have hsub : Subsingleton (↥M ⧸ C.subgroupOf M) := by
    by_contra hns
    have : Nontrivial (↥M ⧸ C.subgroupOf M) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (↥M ⧸ C.subgroupOf M) hsolvQ
  intro m hm
  have h1 : QuotientGroup.mk' (C.subgroupOf M) ⟨m, hm⟩ = 1 := Subsingleton.elim _ _
  have h2 : (⟨m, hm⟩ : ↥M) ∈ C.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
  exact (Subgroup.mem_subgroupOf.mp h2).2

end CFSG.ClassicalInvolution.Asc77.ExactD
