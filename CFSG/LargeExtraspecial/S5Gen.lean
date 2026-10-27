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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.S5

open Subgroup

theorem eq_zero_of_apply_eq_of_sub_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {h : V ≃ₗ[ZMod 2] V} {m : ℕ} (hm : Odd m) (hpow : h ^ m = 1) {v w : V} (hv : h v = v)
    (hw : h w - w = v) : v = 0 := by
  have hhw : h w = w + v := by rw [← hw]; abel
  have key : ∀ i : ℕ, (h ^ i) w = w + (i : ZMod 2) • v := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_smul, hv, hhw]
      push_cast
      rw [add_smul, one_smul]
      abel
  have h1 := key m
  rw [hpow, ZMod.natCast_eq_one_iff_odd.mpr hm, one_smul] at h1
  have h2 : w + v = w + 0 := by rw [← h1]; simp
  exact add_left_cancel h2

theorem dvd_sub_one_or_dvd_add_one {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r : ℤ}
    (h : (p : ℤ) ^ k ∣ r * r - 1) : (p : ℤ) ^ k ∣ r - 1 ∨ (p : ℤ) ^ k ∣ r + 1 := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [show r * r - 1 = (r - 1) * (r + 1) by ring] at h
  by_cases h1 : (p : ℤ) ∣ r + 1
  · right
    have h2 : ¬ (p : ℤ) ∣ r - 1 := by
      intro h2
      have h3 : (p : ℤ) ∣ 2 := by
        have := dvd_sub h1 h2
        rwa [show r + 1 - (r - 1) = 2 by ring] at this
      have h4 : p ∣ 2 := by exact_mod_cast h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
    exact (IsCoprime.pow_left
      ((Irreducible.coprime_iff_not_dvd hp'.irreducible).mpr h2)).dvd_of_dvd_mul_left h
  · left
    exact (IsCoprime.pow_left
      ((Irreducible.coprime_iff_not_dvd hp'.irreducible).mpr h1)).dvd_of_dvd_mul_right h

theorem conj_eq_self_or_inv {X : Type*} [Group X] {k s : X} {p j : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : orderOf k = p ^ j) (hs : s * s = 1)
    (hmem : s * k * s⁻¹ ∈ zpowers k) : s * k * s⁻¹ = k ∨ s * k * s⁻¹ = k⁻¹ := by
  obtain ⟨r, hr⟩ := mem_zpowers_iff.mp hmem
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hconj : ∀ y : X, s * (s * y * s⁻¹) * s⁻¹ = y := by
    intro y
    rw [hsinv]
    calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
      _ = y := by rw [hs, one_mul, mul_one]
  have hpow : ∀ i : ℤ, s * k ^ i * s⁻¹ = (s * k * s⁻¹) ^ i := by
    intro i
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  have hrr : k ^ (r * r - 1) = 1 := by
    have e1 : s * (s * k * s⁻¹) * s⁻¹ = k ^ (r * r) := by
      rw [← hr, hpow, ← hr, ← zpow_mul]
    rw [hconj] at e1
    rw [zpow_sub, zpow_one, ← e1, mul_inv_cancel]
  have hdvd : (p : ℤ) ^ j ∣ r * r - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hrr
    rw [hk] at this
    exact_mod_cast this
  rcases dvd_sub_one_or_dvd_add_one hp hp2 hdvd with h1 | h1
  · left
    have h2 : k ^ (r - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hk]
      exact_mod_cast h1
    rw [← hr, show r = (r - 1) + 1 by ring, zpow_add, h2, one_mul, zpow_one]
  · right
    have h2 : k ^ (r + 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hk]
      exact_mod_cast h1
    rw [← hr, show r = (r + 1) - 1 by ring, zpow_sub, h2, one_mul, zpow_one]

theorem exists_ne_one_commute_of_four_le {X : Type*} [Group X] {A : Subgroup X}
    (hA : ∀ s ∈ A, s * s = 1) (hcard : 4 ≤ Nat.card A) {k : X} {p j : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : orderOf k = p ^ j) (hnorm : ∀ s ∈ A, s * k * s⁻¹ ∈ zpowers k) :
    ∃ t ∈ A, t ≠ 1 ∧ t * k = k * t := by
  classical
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hAfin : (A : Set X).Finite := Set.toFinite _
  have hcard' : 4 ≤ (A : Set X).ncard := by
    rwa [← Nat.card_coe_set_eq]
  obtain ⟨s₁, hs₁A, hs₁⟩ : ∃ s₁ ∈ A, s₁ ≠ 1 := by
    by_contra h
    push Not at h
    have : (A : Set X) ⊆ {1} := fun x hx => h x hx
    have := Set.ncard_le_ncard this (Set.finite_singleton 1)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨s₂, hs₂A, hs₂, hs₁₂⟩ : ∃ s₂ ∈ A, s₂ ≠ 1 ∧ s₂ ≠ s₁ := by
    by_contra h
    push Not at h
    have : (A : Set X) ⊆ {1, s₁} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have := Set.ncard_le_ncard this (Set.toFinite _)
    have h2 := Set.ncard_insert_le (1 : X) ({s₁} : Set X)
    rw [Set.ncard_singleton] at h2
    omega
  have hcomm : ∀ s : X, s * k * s⁻¹ = k → s * k = k * s := by
    intro s hs
    calc s * k = s * k * s⁻¹ * s := by group
      _ = k * s := by rw [hs]
  rcases conj_eq_self_or_inv hp hp2 hk (hA s₁ hs₁A) (hnorm s₁ hs₁A) with h1 | h1
  · exact ⟨s₁, hs₁A, hs₁, hcomm s₁ h1⟩
  rcases conj_eq_self_or_inv hp hp2 hk (hA s₂ hs₂A) (hnorm s₂ hs₂A) with h2 | h2
  · exact ⟨s₂, hs₂A, hs₂, hcomm s₂ h2⟩
  refine ⟨s₁ * s₂, mul_mem hs₁A hs₂A, fun h => hs₁₂ ?_, hcomm _ ?_⟩
  · have : s₂ = s₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right (hA s₁ hs₁A)]
  · calc s₁ * s₂ * k * (s₁ * s₂)⁻¹ = s₁ * (s₂ * k * s₂⁻¹) * s₁⁻¹ := by group
      _ = (s₁ * k * s₁⁻¹)⁻¹ := by rw [h2]; group
      _ = k := by rw [h1, inv_inv]

theorem exists_ne_one_commute_two_of_four_lt {X : Type*} [Group X] {A : Subgroup X}
    (hA : ∀ s ∈ A, s * s = 1) (hcard : 4 < Nat.card A) {k₁ k₂ : X}
    (h₁ : ∀ s ∈ A, s * k₁ * s⁻¹ = k₁ ∨ s * k₁ * s⁻¹ = k₁⁻¹)
    (h₂ : ∀ s ∈ A, s * k₂ * s⁻¹ = k₂ ∨ s * k₂ * s⁻¹ = k₂⁻¹) :
    ∃ t ∈ A, t ≠ 1 ∧ t * k₁ = k₁ * t ∧ t * k₂ = k₂ * t := by
  classical
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite A
  let f : A → Bool × Bool := fun s =>
    (decide ((s : X) * k₁ * (s : X)⁻¹ = k₁), decide ((s : X) * k₂ * (s : X)⁻¹ = k₂))
  have hlt : Fintype.card (Bool × Bool) < Fintype.card A := by
    rw [← Nat.card_eq_fintype_card (α := A)]
    simpa using hcard
  obtain ⟨s₁, s₂, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  have hf₁ := congrArg Prod.fst hf
  have hf₂ := congrArg Prod.snd hf
  simp only [f, decide_eq_decide] at hf₁ hf₂
  have key : ∀ k : X, (∀ s ∈ A, s * k * s⁻¹ = k ∨ s * k * s⁻¹ = k⁻¹) →
      ((s₁ : X) * k * (s₁ : X)⁻¹ = k ↔ (s₂ : X) * k * (s₂ : X)⁻¹ = k) →
      (s₁ * s₂ : X) * k = k * (s₁ * s₂ : X) := by
    intro k hk hiff
    have hconj : (s₁ * s₂ : X) * k * (s₁ * s₂ : X)⁻¹ =
        (s₁ : X) * ((s₂ : X) * k * (s₂ : X)⁻¹) * (s₁ : X)⁻¹ := by group
    have e : (s₁ * s₂ : X) * k * (s₁ * s₂ : X)⁻¹ = k := by
      by_cases h2 : (s₂ : X) * k * (s₂ : X)⁻¹ = k
      · rw [hconj, h2, hiff.mpr h2]
      · have h2' := (hk s₂ s₂.2).resolve_left h2
        have h1' : (s₁ : X) * k * (s₁ : X)⁻¹ = k⁻¹ :=
          (hk s₁ s₁.2).resolve_left fun h1 => h2 (hiff.mp h1)
        rw [hconj, h2', show (s₁ : X) * k⁻¹ * (s₁ : X)⁻¹ = ((s₁ : X) * k * (s₁ : X)⁻¹)⁻¹ by
          group, h1', inv_inv]
    calc (s₁ * s₂ : X) * k = (s₁ * s₂ : X) * k * (s₁ * s₂ : X)⁻¹ * (s₁ * s₂ : X) := by group
      _ = k * (s₁ * s₂ : X) := by rw [e]
  refine ⟨s₁ * s₂, mul_mem s₁.2 s₂.2, fun h => hne ?_, key k₁ h₁ hf₁, key k₂ h₂ hf₂⟩
  apply Subtype.ext
  have h2 : (s₂ : X) = (s₁ : X)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h2, inv_eq_of_mul_eq_one_right (hA s₁ s₁.2)]

theorem eq_three_of_forall_prime_dvd {m : ℕ} (hm : 1 < m)
    (h : ∀ p : ℕ, p.Prime → p ∣ m → p ^ m.factorization p = 3) : m = 3 := by
  have hm0 : m ≠ 0 := by omega
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  obtain ⟨h3, h1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp (h _ hp (Nat.minFac_dvd m))
  rw [h3] at h1
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self m 3
  have hnd := Nat.not_dvd_ordCompl Nat.prime_three hm0
  rw [h1, pow_one] at hsplit hnd
  by_cases hm1 : m / 3 = 1
  · omega
  · exfalso
    have hq := Nat.minFac_prime hm1
    have hqm : (m / 3).minFac ∣ m := (Nat.minFac_dvd _).trans (Dvd.intro_left 3 hsplit)
    obtain ⟨hq3, -⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp (h _ hq hqm)
    have := Nat.minFac_dvd (m / 3)
    rw [hq3] at this
    exact hnd this

theorem exists_ne_one_ne_one_ne {X : Type*} [Group X] {A : Subgroup X} (hcard : 3 ≤ Nat.card A) :
    ∃ u ∈ A, ∃ t ∈ A, u ≠ 1 ∧ t ≠ 1 ∧ u ≠ t := by
  classical
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hcard' : 3 ≤ (A : Set X).ncard := by rwa [← Nat.card_coe_set_eq]
  obtain ⟨u, huA, hu⟩ : ∃ u ∈ A, u ≠ 1 := by
    by_contra h
    push Not at h
    have := Set.ncard_le_ncard (show (A : Set X) ⊆ {1} from fun x hx => h x hx)
      (Set.finite_singleton 1)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨t, htA, ht, hut⟩ : ∃ t ∈ A, t ≠ 1 ∧ t ≠ u := by
    by_contra h
    push Not at h
    have hsub : (A : Set X) ⊆ {1, u} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_insert_le (1 : X) ({u} : Set X)
    rw [Set.ncard_singleton] at h2
    omega
  exact ⟨u, huA, t, htA, hu, ht, Ne.symm hut⟩

end CFSG.LargeExtraspecial.S5
