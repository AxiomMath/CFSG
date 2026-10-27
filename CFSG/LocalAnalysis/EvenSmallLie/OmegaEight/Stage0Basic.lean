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
public import Mathlib.GroupTheory.IndexNormal
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

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup

variable {G : Type*} [Group G]

theorem mul_self_mem_of_relIndex_eq_two {K M : Subgroup G} (h : K.relIndex M = 2) {g : G}
    (hg : g ∈ M) : g * g ∈ K :=
  Subgroup.mul_self_mem_of_index_two h (⟨g, hg⟩ : M)

theorem mem_of_odd_of_relIndex_eq_two {K M : Subgroup G} (h : K.relIndex M = 2) {g : G}
    (hg : g ∈ M) (ho : Odd (orderOf g)) : g ∈ K := by
  obtain ⟨k, hk⟩ := ho
  have h1 : (g * g) ^ k * g = 1 := by
    rw [← sq, ← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
  rw [eq_inv_of_mul_eq_one_right h1]
  exact K.inv_mem (K.pow_mem (mul_self_mem_of_relIndex_eq_two h hg) k)

theorem pow_relIndex_mem_of_le {K M : Subgroup G} (hn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    {g : G} (hg : g ∈ M) : g ^ K.relIndex M ∈ K := by
  have : (K.subgroupOf M).Normal := ⟨fun x hx m => hn m m.2 x hx⟩
  have h := (K.subgroupOf M).pow_index_mem (⟨g, hg⟩ : M)
  rwa [mem_subgroupOf, SubgroupClass.coe_pow] at h

theorem mem_of_coprime_relIndex {K M : Subgroup G} (hn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    {g : G} (hg : g ∈ M) (hc : Nat.Coprime (K.relIndex M) (orderOf g)) : g ∈ K := by
  obtain ⟨n, hn'⟩ := exists_pow_eq_self_of_coprime hc
  rw [← hn']
  exact K.pow_mem (pow_relIndex_mem_of_le hn hg) n

theorem mem_of_pow_mem_of_coprime {K : Subgroup G} {g : G} {a b : ℕ} (ha : g ^ a ∈ K)
    (hb : g ^ b ∈ K) (hab : Nat.Coprime a b) : g ∈ K := by
  have h1 : g = (g ^ a) ^ Nat.gcdA a b * (g ^ b) ^ Nat.gcdB a b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← Nat.gcd_eq_gcd_ab, hab, Nat.cast_one, zpow_one]
  rw [h1]
  exact K.mul_mem (K.zpow_mem ha _) (K.zpow_mem hb _)

theorem exists_pow_coprime_orderOf_eq {g : G} (hg : orderOf g ≠ 0) {p : ℕ} (hp : p.Prime) :
    ∃ m k : ℕ, Nat.Coprime p m ∧ orderOf (g ^ m) = p ^ k := by
  obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgm
    exact hg hgm
  refine ⟨m, k, (Nat.Prime.coprime_iff_not_dvd hp).2 hm, ?_⟩
  rw [orderOf_pow' g hm0, hgm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

theorem mem_sup_zpowers_iff {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) {x : G} :
    x ∈ K ⊔ zpowers g ↔ ∃ k ∈ K, ∃ n : ℤ, x = k * g ^ n := by
  have h := coe_mul_of_right_le_normalizer_left K (zpowers g) (zpowers_le.2 hg)
  rw [← SetLike.mem_coe, h, Set.mem_mul]
  constructor
  · rintro ⟨k, hk, z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
    exact ⟨k, hk, n, rfl⟩
  · rintro ⟨k, hk, n, rfl⟩
    exact ⟨k, hk, g ^ n, zpow_mem (mem_zpowers g) n, rfl⟩

theorem conj_mem_of_relIndex_eq_two {K M : Subgroup G} (h : K.relIndex M = 2) (hKM : K ≤ M)
    {g z : G} (hg : g ∈ M) (hz : z ∈ K) : g * z * g⁻¹ ∈ K :=
  (Subgroup.normal_of_index_eq_two h).conj_mem ⟨z, hKM hz⟩ hz ⟨g, hg⟩

theorem mul_mem_of_not_mem_of_relIndex_eq_two {K M : Subgroup G} (h : K.relIndex M = 2)
    {a b : G} (ha : a ∈ M) (hb : b ∈ M) (haK : a ∉ K) (hbK : b ∉ K) : a * b ∈ K :=
  (Subgroup.mul_mem_iff_of_index_two h (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2 (iff_of_false haK hbK)

theorem exists_not_mem_pow_mem [Finite G] {K M : Subgroup G}
    (hn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ K.relIndex M) : ∃ g ∈ M, g ∉ K ∧ g ^ p ∈ K := by
  have : Fact p.Prime := ⟨hp⟩
  have : (K.subgroupOf M).Normal := ⟨fun x hx m => hn m m.2 x hx⟩
  have hcard : p ∣ Nat.card (M ⧸ K.subgroupOf M) := by rw [← index_eq_card]; exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hcard
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, g.2, fun hgK => ?_, ?_⟩
  · have h1 : ((g : M ⧸ K.subgroupOf M)) = 1 := (QuotientGroup.eq_one_iff g).2 hgK
    rw [h1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · have h1 : ((g : M ⧸ K.subgroupOf M)) ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    rwa [mem_subgroupOf, SubgroupClass.coe_pow] at h1

theorem eq_of_relIndex_prime {N M H : Subgroup G} (hNM : N ≤ M) (hMH : M ≤ H)
    (hp : (N.relIndex H).Prime) {x : G} (hxM : x ∈ M) (hxN : x ∉ N) : M = H := by
  have h := relIndex_mul_relIndex N M H hNM hMH
  have h1 : N.relIndex M ≠ 1 := fun h1 => hxN (relIndex_eq_one.1 h1 hxM)
  have h2 : M.relIndex H = 1 := by
    rw [← h] at hp
    rcases Nat.prime_mul_iff.1 hp with ⟨-, h3⟩ | ⟨-, h3⟩
    · exact h3
    · exact absurd h3 h1
  exact le_antisymm hMH (relIndex_eq_one.1 h2)

theorem eq_of_mem_zpowers_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2) (hy : y ∈ zpowers x)
    (hy1 : y ≠ 1) : y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hx] at hy1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h] at hy1 ⊢
  · exact absurd (zpow_zero x) hy1
  · exact zpow_one x

theorem exists_conj_mem_of_card_quotient [Finite G] {I : Subgroup G} [I.Normal] {m : ℕ}
    (hcard : Nat.card (G ⧸ I) = 2 * m) (hm : Odd m) {β : G} (hβ2 : β * β ∈ I) (hβI : β ∉ I)
    {α : G} (hαI : α ∉ I) (hα : α * α ∈ I) : ∃ γ : G, α⁻¹ * (γ * β * γ⁻¹) ∈ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ z : G, z ∉ I → z * z ∈ I → orderOf (z : G ⧸ I) = 2 := by
    intro z hz hz2
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hz2
    · rwa [Ne, QuotientGroup.eq_one_iff]
  have hsyl : ∀ z : G ⧸ I, orderOf z = 2 → IsPGroup 2 (zpowers z) ∧ ¬ 2 ∣ (zpowers z).index := by
    intro z hz
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), ?_⟩
    have h := (zpowers z).card_mul_index
    rw [Nat.card_zpowers, hz, hcard] at h
    have h' : (zpowers z).index = m := by omega
    have hm2 := Nat.odd_iff.mp hm
    rw [h']
    omega
  obtain ⟨hpx, hix⟩ := hsyl _ (hord α hαI hα)
  obtain ⟨hpy, hiy⟩ := hsyl _ (hord β hβI hβ2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ I) (hpy.toSylow hiy) (hpx.toSylow hix)
  have hmem : g * (β : G ⧸ I) * g⁻¹ ∈ zpowers (α : G ⧸ I) := by
    have h1 : (β : G ⧸ I) ∈ (hpy.toSylow hiy : Subgroup (G ⧸ I)) := by
      rw [IsPGroup.toSylow_coe]
      exact mem_zpowers _
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ h1
    rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe] at h2
    exact h2
  have hne : g * (β : G ⧸ I) * g⁻¹ ≠ 1 := by
    intro h1
    have h2 : (β : G ⧸ I) = 1 := by
      calc (β : G ⧸ I) = g⁻¹ * (g * (β : G ⧸ I) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact hβI ((QuotientGroup.eq_one_iff β).1 h2)
  have heq := eq_of_mem_zpowers_of_orderOf_eq_two (hord α hαI hα) hmem hne
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨γ, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact heq.symm

end CFSG.EvenSmallLie.OmegaEight.Stage0
