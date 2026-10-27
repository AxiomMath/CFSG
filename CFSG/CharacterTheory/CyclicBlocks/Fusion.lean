module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
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

namespace CFSG.CyclicBlocks

variable {G : Type*} [Group G]

theorem prime_pow_dvd_sub_one_or_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b : ℕ} {k : ℤ}
    (h : ((p ^ b : ℕ) : ℤ) ∣ (k - 1) * (k + 1)) :
    ((p ^ b : ℕ) : ℤ) ∣ k - 1 ∨ ((p ^ b : ℕ) : ℤ) ∣ k + 1 := by
  have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).irreducible
  by_cases h1 : (p : ℤ) ∣ k - 1
  · left
    have h2 : ¬ (p : ℤ) ∣ k + 1 := by
      intro h2
      have h3 : (p : ℤ) ∣ 2 := by
        have h4 := dvd_sub h2 h1
        rwa [show k + 1 - (k - 1) = 2 by ring] at h4
      have h4 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h3
      have h5 := hp.two_le
      omega
    have hcop : IsCoprime ((p ^ b : ℕ) : ℤ) (k + 1) := by
      rw [Nat.cast_pow]
      exact ((hirr.coprime_iff_not_dvd).mpr h2).pow_left
    exact hcop.dvd_of_dvd_mul_right h
  · right
    have hcop : IsCoprime ((p ^ b : ℕ) : ℤ) (k - 1) := by
      rw [Nat.cast_pow]
      exact ((hirr.coprime_iff_not_dvd).mpr h1).pow_left
    exact hcop.dvd_of_dvd_mul_left h

section Action

variable {p : ℕ} {u : G}

theorem conj_eq_or_inv_of_mem_normalizer_of_dvd_prime_pow (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (hu : orderOf u ∣ p ^ e)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {g : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹ := by
  have hmem : g * u * g⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp hg u).mp (Subgroup.mem_zpowers u)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsq : g * g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    have h := Subgroup.mul_self_mem_of_index_two hindex ⟨g, hg⟩
    rwa [Subgroup.mem_subgroupOf] at h
  have hsqu : (g * g) * u * (g * g)⁻¹ = u := by
    have hc := Subgroup.mem_centralizer_iff.mp hsq u (Subgroup.mem_zpowers u)
    rw [← hc]
    group
  have hkk : u ^ (k * k) = u := by
    calc u ^ (k * k) = (u ^ k) ^ k := by rw [zpow_mul]
      _ = (g * u * g⁻¹) ^ k := by rw [hk]
      _ = g * u ^ k * g⁻¹ := conj_zpow
      _ = g * (g * u * g⁻¹) * g⁻¹ := by rw [hk]
      _ = (g * g) * u * (g * g)⁻¹ := by group
      _ = u := hsqu
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hu
  have hdvd : ((p ^ b : ℕ) : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← hb, orderOf_dvd_iff_zpow_eq_one]
    have hring : (k - 1) * (k + 1) = k * k - 1 := by ring
    rw [hring, zpow_sub, hkk, zpow_one, mul_inv_cancel]
  rcases prime_pow_dvd_sub_one_or_add_one hp hp2 hdvd with h | h
  · left
    rw [← hk]
    have h1 : u ^ (k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hb]
      exact h
    calc u ^ k = u ^ (k - 1) * u := by rw [← zpow_add_one, sub_add_cancel]
      _ = u := by rw [h1, one_mul]
  · right
    rw [← hk]
    have h1 : u ^ (k + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hb]
      exact h
    calc u ^ k = u ^ (k + 1) * u⁻¹ := by rw [zpow_add_one, mul_inv_cancel_right]
      _ = u⁻¹ := by rw [h1, one_mul]

theorem mem_centralizer_zpowers_of_conj_eq {g : G} (h : g * u * g⁻¹ = u) :
    g ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hm : g * u ^ m * g⁻¹ = u ^ m := by rw [← conj_zpow, h]
  calc u ^ m * g = g * u ^ m * g⁻¹ * g := by rw [hm]
    _ = g * u ^ m := by group

theorem exists_mem_normalizer_conj_eq_inv_of_dvd_prime_pow (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (hu : orderOf u ∣ p ^ e)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) :
    ∃ n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G),
      n ∉ Subgroup.centralizer (Subgroup.zpowers u : Set G) ∧ n * u * n⁻¹ = u⁻¹ := by
  have hnle : ¬ Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
    intro hle
    rw [← Subgroup.relIndex_eq_one] at hle
    omega
  obtain ⟨n, hn, hnc⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  refine ⟨n, hn, hnc, ?_⟩
  rcases conj_eq_or_inv_of_mem_normalizer_of_dvd_prime_pow hp hp2 hu hindex hn with h | h
  · exact absurd (mem_centralizer_zpowers_of_conj_eq h) hnc
  · exact h

theorem inv_ne_self_of_relIndex_eq_two (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (hu : orderOf u ∣ p ^ e)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) :
    u⁻¹ ≠ u := by
  intro hinv
  obtain ⟨n, -, hnc, hn⟩ := exists_mem_normalizer_conj_eq_inv_of_dvd_prime_pow hp hp2 hu hindex
  rw [hinv] at hn
  exact hnc (mem_centralizer_zpowers_of_conj_eq hn)

theorem conj_mem_zpowers_eq_or_inv {g x : G} (hx : x ∈ Subgroup.zpowers u)
    (hg : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹) : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases hg with h | h
  · left
    rw [← conj_zpow, h]
  · right
    rw [← conj_zpow, h, inv_zpow]

theorem conj_mem_zpowers_eq_inv {g x : G} (hx : x ∈ Subgroup.zpowers u) (hg : g * u * g⁻¹ = u⁻¹) :
    g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hg, inv_zpow]

theorem eq_one_of_inv_eq_self_of_odd {x : G} (hodd : Odd (orderOf x)) (h : x⁻¹ = x) : x = 1 := by
  have hsq : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel x
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem odd_orderOf_of_dvd_prime_pow (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ} {x : G}
    (hx : orderOf x ∣ p ^ e) : Odd (orderOf x) :=
  Odd.of_dvd_nat ((hp.eq_two_or_odd'.resolve_left hp2).pow) hx

theorem mem_centralizer_of_mem_normalizer_of_commute (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (hu : orderOf u ∣ p ^ e)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x : G} (hx : x ∈ Subgroup.zpowers u) (hx1 : x ≠ 1) {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G)) (hgx : Commute g x) :
    g * u * g⁻¹ = u := by
  rcases conj_eq_or_inv_of_mem_normalizer_of_dvd_prime_pow hp hp2 hu hindex hg with h | h
  · exact h
  · exfalso
    apply hx1
    have hxodd : Odd (orderOf x) :=
      odd_orderOf_of_dvd_prime_pow hp hp2 ((orderOf_dvd_of_mem_zpowers hx).trans hu)
    refine eq_one_of_inv_eq_self_of_odd hxodd ?_
    rcases conj_mem_zpowers_eq_or_inv hx (Or.inr h) with h' | h'
    ·
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : g * u ^ j * g⁻¹ = u ^ j := by rw [hgx.eq, mul_inv_cancel_right]
      have hi : g * u ^ j * g⁻¹ = (u ^ j)⁻¹ := by rw [← conj_zpow, h, inv_zpow]
      rw [← hi, hc]
    · have hc : g * x * g⁻¹ = x := by rw [hgx.eq, mul_inv_cancel_right]
      rw [← h', hc]

end Action

section Sylow

variable [Finite G] {p : ℕ} [Fact p.Prime] {u : G}

theorem orderOf_dvd_of_sylow_eq_zpowers (P : Sylow p G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) :
    orderOf u ∣ p ^ (Nat.card G).factorization p := by
  rw [← Nat.card_zpowers, ← hPu, Sylow.card_eq_multiplicity]

theorem card_sylow_odd_three_le (hp2 : p ≠ 2) (P : Sylow p G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) :
    orderOf u = Nat.card P ∧ Nat.card P % 2 = 1 ∧ 3 ≤ Nat.card P := by
  have hp : p.Prime := Fact.out
  have hu := orderOf_dvd_of_sylow_eq_zpowers P hPu
  have hcard : orderOf u = Nat.card P := by rw [← Nat.card_zpowers, ← hPu]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hu
  have hodd : Odd (orderOf u) := odd_orderOf_of_dvd_prime_pow hp hp2 hu
  have hne : u ≠ 1 := by
    intro h
    exact inv_ne_self_of_relIndex_eq_two hp hp2 hu hindex (by rw [h, inv_one])
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hb
    exact hne (orderOf_eq_one_iff.mp hb)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine ⟨hcard, ?_, ?_⟩
  · rw [← hcard]
    exact Nat.odd_iff.mp hodd
  · rw [← hcard, hb]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hb0)

theorem eq_or_eq_inv_of_isConj (hp2 : p ≠ 2) (P : Sylow p G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x y : G} (hx : x ∈ Subgroup.zpowers u) (hy : y ∈ Subgroup.zpowers u) (hxy : IsConj x y) :
    y = x ∨ y = x⁻¹ := by
  have hp : p.Prime := Fact.out
  have hu := orderOf_dvd_of_sylow_eq_zpowers P hPu
  have : IsMulCommutative (P : Subgroup G) := by
    rw [hPu]
    infer_instance
  have hmemP : ∀ z ∈ Subgroup.zpowers u, z ∈ P := by
    intro z hz
    rw [← SetLike.mem_coe]
    show z ∈ ((P : Subgroup G) : Set G)
    rw [hPu]
    exact hz
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hyP : c⁻¹⁻¹ * x * c⁻¹ ∈ P := by
    rw [inv_inv, hc]
    exact hmemP y hy
  obtain ⟨m, hm, hmeq⟩ := P.conj_eq_normalizer_conj_of_mem x c⁻¹ (hmemP x hx) hyP
  rw [inv_inv, hc] at hmeq
  have hm' : m⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [← hPu]
    exact Subgroup.inv_mem _ hm
  have hact := conj_mem_zpowers_eq_or_inv hx
    (conj_eq_or_inv_of_mem_normalizer_of_dvd_prime_pow hp hp2 hu hindex hm')
  rw [inv_inv] at hact
  rw [hmeq]
  exact hact

omit [Finite G] [Fact p.Prime] in
theorem zpowers_le_centralizer_zpowers {x : G} (hx : x ∈ Subgroup.zpowers u) :
    Subgroup.zpowers u ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mul, ← zpow_add, ← zpow_add, add_comm]

theorem exists_normal_complement_centralizer (hp2 : p ≠ 2) (P : Sylow p G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x : G} (hx : x ∈ Subgroup.zpowers u) (hx1 : x ≠ 1) :
    ∃ (R : Subgroup (Subgroup.centralizer (Subgroup.zpowers x : Set G))) (_ : R.Normal),
      Nat.Coprime p (Nat.card R) ∧
        IsPGroup p (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⧸ R) := by
  have hp : p.Prime := Fact.out
  have hu := orderOf_dvd_of_sylow_eq_zpowers P hPu
  set C := Subgroup.centralizer (Subgroup.zpowers x : Set G) with hC
  have hle : (P : Subgroup G) ≤ C := hPu ▸ zpowers_le_centralizer_zpowers hx
  let S : Sylow p C := P.subtype hle
  have hS : (S : Subgroup C) ≤ CFSG.centerIn (Subgroup.normalizer (S : Subgroup C)) := by
    intro s hs
    refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : (g : G) ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
      have h : g ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf C := by
        rw [Subgroup.subgroupOf_normalizer_eq hle]
        exact hg
      rw [Subgroup.mem_subgroupOf, hPu] at h
      exact h
    have hgx : Commute (g : G) x :=
      ((Subgroup.mem_centralizer_iff.mp g.2 x (Subgroup.mem_zpowers x))).symm
    have hgu := mem_centralizer_of_mem_normalizer_of_commute hp hp2 hu hindex hx hx1 hg' hgx
    have hsP : (s : G) ∈ Subgroup.zpowers u := by
      have h : s ∈ (P : Subgroup G).subgroupOf C := hs
      rw [Subgroup.mem_subgroupOf, hPu] at h
      exact h
    have hcomm := Subgroup.mem_centralizer_iff.mp (mem_centralizer_zpowers_of_conj_eq hgu) _ hsP
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcomm.symm
  exact CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p S hS

end Sylow

end CFSG.CyclicBlocks
