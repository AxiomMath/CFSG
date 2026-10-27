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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.ComponentClassification.M12Cover.CyclicKernel

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by rfl, h, zpow_one]

theorem exists_mul_of_mem_sup_of_commute {K N : Subgroup G}
    (hc : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k) {x : G} (hx : x ∈ K ⊔ N) :
    ∃ k ∈ K, ∃ n ∈ N, x = k * n := by
  have hrange := MonoidHom.noncommCoprod_range K.subtype N.subtype
    (fun k n => show Commute (K.subtype k) (N.subtype n) from hc k k.2 n n.2)
  rw [range_subtype, range_subtype] at hrange
  rw [← hrange] at hx
  obtain ⟨⟨k, n⟩, rfl⟩ := hx
  exact ⟨k, k.2, n, n.2, MonoidHom.noncommCoprod_apply _ _ _ _⟩

theorem card_sup_of_commute {K N : Subgroup G} (hc : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k)
    (hKN : K ⊓ N = ⊥) : Nat.card (K ⊔ N : Subgroup G) = Nat.card K * Nat.card N := by
  set f := K.subtype.noncommCoprod N.subtype
    (fun k n => show Commute (K.subtype k) (N.subtype n) from hc k k.2 n n.2) with hf
  have hinj : Function.Injective f := by
    rw [hf, MonoidHom.noncommCoprod_injective, range_subtype, range_subtype, disjoint_iff]
    exact ⟨K.subtype_injective, N.subtype_injective, hKN⟩
  have hrange : f.range = K ⊔ N := by
    rw [hf, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange]

theorem commute_of_mem_sup_of_commute {E A : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hc : ∀ x ∈ E, ∀ y ∈ A, x * y = y * x) {x m : G} (hx : x ∈ E) (hm : m ∈ E ⊔ A) :
    x * m = m * x := by
  obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hm
  rw [← mul_assoc, hE x hx e he, mul_assoc, hc x hx a ha, ← mul_assoc]

theorem commutator_sup_eq_of_commute {E A : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hc : ∀ x ∈ E, ∀ y ∈ A, x * y = y * x) : ⁅E ⊔ A, E ⊔ A⁆ = ⁅A, A⁆ := by
  refine le_antisymm ?_ (commutator_mono le_sup_right le_sup_right)
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨e₁, he₁, a₁, ha₁, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hx
  obtain ⟨e₂, he₂, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hy
  have hm : a₁ * (e₂ * a₂) * a₁⁻¹ ∈ E ⊔ A :=
    mul_mem (mul_mem (mem_sup_right ha₁) hy) (inv_mem (mem_sup_right ha₁))
  have h1 : e₁ * (a₁ * (e₂ * a₂) * a₁⁻¹) * e₁⁻¹ = a₁ * (e₂ * a₂) * a₁⁻¹ := by
    rw [commute_of_mem_sup_of_commute hE hc he₁ hm, mul_inv_cancel_right]
  have hcA : ⁅a₁, a₂⁆ ∈ A := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)
  have h2 : e₂ * ⁅a₁, a₂⁆ * e₂⁻¹ = ⁅a₁, a₂⁆ := by
    rw [hc e₂ he₂ _ hcA, mul_inv_cancel_right]
  have h3 : a₁ * e₂ = e₂ * a₁ := (hc e₂ he₂ a₁ ha₁).symm
  have key : ⁅e₁ * a₁, e₂ * a₂⁆ = ⁅a₁, a₂⁆ := by
    calc ⁅e₁ * a₁, e₂ * a₂⁆
        = e₁ * (a₁ * (e₂ * a₂) * a₁⁻¹) * e₁⁻¹ * (e₂ * a₂)⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a₁ * e₂ * a₂ * a₁⁻¹ * (e₂ * a₂)⁻¹ := by rw [h1]; group
      _ = e₂ * ⁅a₁, a₂⁆ * e₂⁻¹ := by rw [h3, commutatorElement_def]; group
      _ = ⁅a₁, a₂⁆ := h2
  rw [key]
  exact commutator_mem_commutator ha₁ ha₂

theorem mem_or_mul_mem_of_mem_sup_zpowers {K : Subgroup G} {p : G}
    (hpN : p ∈ normalizer (K : Set G)) (hp2 : p * p = 1) {x : G} (hx : x ∈ K ⊔ zpowers p) :
    x ∈ K ∨ x * p ∈ K := by
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
  have hconj : ∀ y, y ∈ K → p * y * p⁻¹ ∈ K := fun y hy => (mem_normalizer_iff.mp hpN y).mp hy
  let M : Subgroup G :=
    { carrier := {x | x ∈ K ∨ x * p ∈ K}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (K.mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact K.mul_mem hx hy)
        · right
          have h : x * y * p = x * p * (p * y * p⁻¹) := by
            rw [hpinv]
            calc x * y * p = x * (p * p) * y * p := by rw [hp2, mul_one]
              _ = x * p * (p * y * p) := by group
          rw [h]
          exact K.mul_mem hx (hconj y hy)
        · left
          have h : x * y = x * p * (p * (y * p) * p⁻¹) := by
            calc x * y = x * (p * p) * y * (p * p⁻¹) := by
                  rw [hp2, mul_one, mul_inv_cancel, mul_one]
              _ = x * p * (p * (y * p) * p⁻¹) := by group
          rw [h]
          exact K.mul_mem hx (hconj _ hy)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (K.inv_mem hx)
        · right
          have h : x⁻¹ * p = p * (x * p)⁻¹ * p⁻¹ := by rw [hpinv]; group
          rw [h]
          exact hconj _ (K.inv_mem hx) }
  have hle : K ⊔ zpowers p ≤ M :=
    sup_le (fun y hy => Or.inl hy) (zpowers_le.mpr (Or.inr (by rw [hp2]; exact K.one_mem)))
  exact hle hx

theorem eq_of_orderOf_eq_two_of_isCyclic [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    {x y : G} (hx : x ∈ K) (hy : y ∈ K) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : x = y := by
  classical
  have := Fintype.ofFinite K
  have h2 : 2 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← hx2]
    exact Subgroup.orderOf_dvd_natCard K hx
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h2
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : (⟨x, hx⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  have hya : (⟨y, hy⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  rw [Finset.mem_singleton] at hxa hya
  exact congrArg Subtype.val (hxa.trans hya.symm)

theorem eq_one_or_eq_of_sq_eq_one_of_isCyclic [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    {t x : G} (ht : t ∈ K) (ht2 : orderOf t = 2) (hx : x ∈ K) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = t := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · exact Or.inr (eq_of_orderOf_eq_two_of_isCyclic hK hx ht (orderOf_eq_prime hx2 h1) ht2)

theorem mul_comm_of_isCyclic {K : Subgroup G} (hK : IsCyclic K) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : x * y = y * x := by
  have := hK
  have h := (IsCyclic.isMulCommutative (α := K)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val h

theorem exists_orderOf_eq_four_of_isCyclic [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    (hK2 : IsPGroup 2 K) (hcard : 2 < Nat.card K) : ∃ a ∈ K, orderOf a = 4 := by
  have := hK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have h4 : 4 ∣ Nat.card K := by
    rw [hn]
    have h2n : 2 ≤ n := by
      by_contra h
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> rw [hn] at hcard <;> norm_num at hcard
    exact (pow_dvd_pow 2 h2n : 2 ^ 2 ∣ 2 ^ n)
  refine ⟨((γ ^ (orderOf γ / 4) : K) : G), (γ ^ (orderOf γ / 4)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (by rw [hγ]; exact Nat.card_pos.ne') (by rw [hγ]; exact h4)

theorem orderOf_eq_four_of_sq {a t : G} (ha : a ^ 2 = t) (ht : orderOf t = 2) :
    orderOf a = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a)
    (by rw [pow_one, ha]; exact fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide))
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, ha, ← ht, pow_orderOf_eq_one])
  rw [h]
  norm_num

theorem eq_or_eq_inv_of_orderOf_eq_four [Finite G] {K : Subgroup G} (hK : IsCyclic K) {a x : G}
    (ha : a ∈ K) (hx : x ∈ K) (ha4 : orderOf a = 4) (hx4 : orderOf x = 4) : x = a ∨ x = a⁻¹ := by
  classical
  have := Fintype.ofFinite K
  have h4 : 4 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← ha4]
    exact Subgroup.orderOf_dvd_natCard K ha
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h4
  rw [show Nat.totient 4 = 2 by decide] at h
  have hne : (⟨a, ha⟩ : K) ≠ ⟨a⁻¹, inv_mem ha⟩ := by
    intro he
    have h1 : a * a = 1 := by
      have h' : a = a⁻¹ := congrArg Subtype.val he
      calc a * a = a * a⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel a
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h1])
    rw [ha4] at h2
    exact absurd h2 (by decide)
  have hsub : ({⟨a, ha⟩, ⟨a⁻¹, inv_mem ha⟩} : Finset K) ⊆
      Finset.univ.filter fun y : K => orderOf y = 4 := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_filter]
    rcases hy with rfl | rfl
    · exact ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, ha4]⟩
    · exact ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, orderOf_inv, ha4]⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h, Finset.card_pair hne])
  have hxm : (⟨x, hx⟩ : K) ∈ Finset.univ.filter fun y : K => orderOf y = 4 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, hx4]⟩
  rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hxm
  rcases hxm with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

theorem exists_pow_orderOf_eq_four [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    (hK2 : IsPGroup 2 K) {t s : G} (ht : t ∈ K) (ht2 : orderOf t = 2) (hs : s ∈ K)
    (hs1 : s ≠ 1) (hst : s ≠ t) : ∃ n : ℕ, orderOf (s ^ n) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
  have hsd : orderOf s ∣ 2 ^ n := by rw [← hn]; exact Subgroup.orderOf_dvd_natCard K hs
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hsd
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · exact hs1 (orderOf_eq_one_iff.mp (by rw [hm, pow_zero]))
    · exact hst (eq_of_orderOf_eq_two_of_isCyclic hK hs ht (by rw [hm, pow_one]) ht2)
  refine ⟨orderOf s / 4, orderOf_pow_orderOf_div (orderOf_pos s).ne' ?_⟩
  rw [hm]
  exact (pow_dvd_pow 2 hm2 : 2 ^ 2 ∣ 2 ^ m)

section LargeKernel

variable {T : Subgroup G} {t a : G}

theorem mem_centralizer_of_conj_mem
    (hsq : ∀ h ∈ centralizer {t}, ∀ s ∈ T, h ^ 2 * s = s * h ^ 2)
    (hobs : ∀ g : G, (∀ s ∈ T, g⁻¹ * s * g ∈ centralizer {t}) → g ∈ centralizer {t})
    (ha : a ^ 2 = t) {g : G} (hg : g * a * g⁻¹ ∈ centralizer {t}) : g ∈ centralizer {t} := by
  apply hobs
  intro s hs
  have h := hsq _ hg s hs
  rw [conj_pow, ha] at h
  rw [mem_centralizer_singleton_iff]
  calc g⁻¹ * s * g * t = g⁻¹ * (s * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹ * s) * g := by rw [h]
    _ = t * (g⁻¹ * s * g) := by group

theorem eq_of_isConj_of_commute
    (hsq : ∀ h ∈ centralizer {t}, ∀ s ∈ T, h ^ 2 * s = s * h ^ 2)
    (hobs : ∀ g : G, (∀ s ∈ T, g⁻¹ * s * g ∈ centralizer {t}) → g ∈ centralizer {t})
    (ha : a ^ 2 = t) {q : G} (hq : IsConj t q) (hqa : q * a = a * q) : q = t := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hq
  have hc : c⁻¹ * a * c⁻¹⁻¹ ∈ centralizer {t} := by
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * a * c⁻¹⁻¹ * t = c⁻¹ * (a * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * t * c⁻¹ * a) * c := by rw [hqa]
      _ = t * (c⁻¹ * a * c⁻¹⁻¹) := by group
  have hc' := inv_mem (mem_centralizer_of_conj_mem hsq hobs ha hc)
  rw [inv_inv, mem_centralizer_singleton_iff] at hc'
  rw [hc', mul_inv_cancel_right]

theorem conj_eq_inv_of_isConj [Finite G] (hTc : IsCyclic T) (ht : orderOf t = 2)
    (hsq : ∀ h ∈ centralizer {t}, ∀ s ∈ T, h ^ 2 * s = s * h ^ 2)
    (hobs : ∀ g : G, (∀ s ∈ T, g⁻¹ * s * g ∈ centralizer {t}) → g ∈ centralizer {t})
    (haT : a ∈ T) (ha : a ^ 2 = t) {q : G} (hqT : q * a * q⁻¹ ∈ T) (hq : IsConj t q)
    (hqt : q ≠ t) : q * a * q⁻¹ = a⁻¹ := by
  have ha4 := orderOf_eq_four_of_sq ha ht
  have hc4 : orderOf (q * a * q⁻¹) = 4 := by
    rw [show q * a * q⁻¹ = MulAut.conj q a from rfl, MulEquiv.orderOf_eq, ha4]
  rcases eq_or_eq_inv_of_orderOf_eq_four hTc haT hqT ha4 hc4 with h | h
  · exact absurd (eq_of_isConj_of_commute hsq hobs ha hq (mul_inv_eq_iff_eq_mul.mp h)) hqt
  · exact h

theorem eq_one_or_eq_of_isConj_of_commute [Finite G] (hTc : IsCyclic T) (hT2 : IsPGroup 2 T)
    (htT : t ∈ T) (ht : orderOf t = 2)
    (hsq : ∀ h ∈ centralizer {t}, ∀ s ∈ T, h ^ 2 * s = s * h ^ 2)
    (hobs : ∀ g : G, (∀ s ∈ T, g⁻¹ * s * g ∈ centralizer {t}) → g ∈ centralizer {t})
    (haT : a ∈ T) (ha : a ^ 2 = t) {q : G} (hq : IsConj t q) (hqt : q ≠ t) {s : G}
    (hs : s ∈ T) (hqs : q * s = s * q) : s = 1 ∨ s = t := by
  by_contra hne
  push Not at hne
  obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_four hTc hT2 htT ht hs hne.1 hne.2
  have hqn : q * s ^ n = s ^ n * q := ((Commute.pow_right hqs n : Commute q (s ^ n)))
  rcases eq_or_eq_inv_of_orderOf_eq_four hTc haT (pow_mem hs n)
      (orderOf_eq_four_of_sq ha ht) hn with h | h
  · rw [h] at hqn
    exact hqt (eq_of_isConj_of_commute hsq hobs ha hq hqn)
  · rw [h] at hqn
    have hqa : q * a = a * q := by
      have := congrArg (fun x => x⁻¹) hqn
      simp only [mul_inv_rev, inv_inv] at this
      calc q * a = q * (a * q⁻¹) * q := by group
        _ = q * (q⁻¹ * a) * q := by rw [this]
        _ = a * q := by group
    exact hqt (eq_of_isConj_of_commute hsq hobs ha hq hqa)

end LargeKernel

theorem conj_eq_of_mem_normalizer_of_center_eq_zpowers {L : Subgroup G} {t : L}
    (hZ : center L = zpowers t) (ht : orderOf t = 2) {h : G}
    (hh : h ∈ normalizer (L : Set G)) : h * t * h⁻¹ = t := by
  have hmem : ∀ x, x ∈ L ↔ h * x * h⁻¹ ∈ L := mem_normalizer_iff.mp hh
  have htZ : t ∈ center L := hZ ▸ mem_zpowers t
  have hu : (⟨h * t * h⁻¹, (hmem t).mp t.2⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro m
    have hm' : h⁻¹ * m * h ∈ L := by
      refine (hmem _).mpr ?_
      rw [show h * (h⁻¹ * m * h) * h⁻¹ = m by group]
      exact m.2
    have htc := congrArg Subtype.val (mem_center_iff.mp htZ ⟨h⁻¹ * m * h, hm'⟩)
    simp only [Subgroup.coe_mul] at htc
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (m : G) * (h * t * h⁻¹) = h * ((h⁻¹ * m * h) * t) * h⁻¹ := by group
      _ = h * (t * (h⁻¹ * m * h)) * h⁻¹ := by rw [htc]
      _ = h * t * h⁻¹ * m := by group
  rw [hZ] at hu
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hu with h1 | h1
  · exfalso
    have h1' : h * (t : G) * h⁻¹ = 1 := congrArg Subtype.val h1
    have ht1 : (t : G) = 1 := by
      calc (t : G) = h⁻¹ * (h * t * h⁻¹) * h := by group
        _ = 1 := by rw [h1']; group
    have : t = 1 := Subtype.ext ht1
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · exact congrArg Subtype.val h1

theorem centralizer_closure_pair (t p : G) :
    centralizer (closure ({t, p} : Set G) : Set G) = centralizer {t} ⊓ centralizer {p} := by
  ext x
  rw [centralizer_closure, mem_inf, mem_centralizer_iff, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

theorem closure_triple_eq_sup (t p w : G) :
    closure ({t, p, w} : Set G) = closure ({t, p} : Set G) ⊔ zpowers w := by
  rw [zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_union, Set.singleton_union]

end CFSG.ComponentClassification.M12Cover.CyclicKernel
