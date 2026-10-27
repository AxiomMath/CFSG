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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.CGT.T75I

open Equiv Equiv.Perm

section PermFacts

variable {k : ℕ}

theorem card_support_of_even_involution (hk : k ≤ 7) {σ : Perm (Fin k)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) (hs : sign σ = 1) : σ.support.card = 4 := by
  classical
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have hdvd : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2' : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have := (Nat.dvd_prime Nat.prime_two).1 (hdvd.trans hord)
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 hall
  set j := Multiset.card σ.cycleType with hj
  have hsum : σ.cycleType.sum = 2 * j := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsupp : σ.support.card = 2 * j := by rw [← Equiv.Perm.sum_cycleType, hsum]
  have hsg := Equiv.Perm.sign_of_cycleType σ
  rw [hs, hsum, ← hj] at hsg
  have hj0 : j ≠ 0 := by
    intro h0
    exact h1 (Equiv.Perm.cycleType_eq_zero.1 (Multiset.card_eq_zero.1 h0))
  have hle : σ.support.card ≤ k := by
    simpa using Finset.card_le_univ σ.support
  have heven : Even j := by
    have h3 : (-1 : ℤˣ) ^ (2 * j + j) = 1 := hsg.symm
    have h4 : (-1 : ℤˣ) ^ (2 * j + j) = (-1 : ℤˣ) ^ j := by
      rw [pow_add, pow_mul]
      simp
    rw [h4] at h3
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at h3
    exact absurd h3 (by decide)
  obtain ⟨m, hm⟩ := heven
  omega

theorem card_fixedPoints_of_even_involution (hk : k ≤ 7) {σ : Perm (Fin k)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) (hs : sign σ = 1) : Fintype.card (Function.fixedPoints σ) = k - 4 := by
  classical
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    card_support_of_even_involution hk h2 h1 hs]
  simp

theorem cycleType_of_even_involution (hk : k ≤ 7) {σ : Perm (Fin k)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) (hs : sign σ = 1) : σ.cycleType = Multiset.replicate 2 2 := by
  classical
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have hdvd : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2' : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have := (Nat.dvd_prime Nat.prime_two).1 (hdvd.trans hord)
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 hall
  have hsupp := card_support_of_even_involution hk h2 h1 hs
  have hsum : σ.cycleType.sum = 2 * Multiset.card σ.cycleType := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
    simp
  have hj : Multiset.card σ.cycleType = 2 := by
    rw [← Equiv.Perm.sum_cycleType] at hsupp
    omega
  rw [hrep, hj]

theorem exists_even_conj_of_even_involutions (hk6 : 6 ≤ k) (hk7 : k ≤ 7) {a b : Perm (Fin k)}
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (has : sign a = 1) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1)
    (hbs : sign b = 1) : ∃ g : Perm (Fin k), sign g = 1 ∧ g * a * g⁻¹ = b := by
  classical
  have hconj : IsConj a b := isConj_iff_cycleType_eq.2 (by
    rw [cycleType_of_even_involution hk7 ha2 ha1 has, cycleType_of_even_involution hk7 hb2 hb1 hbs])
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  rcases Int.units_eq_one_or (sign g) with hs | hs
  · exact ⟨g, hs, hg⟩
  · have hfix : 2 ≤ Fintype.card (Function.fixedPoints a) := by
      rw [card_fixedPoints_of_even_involution hk7 ha2 ha1 has]
      omega
    obtain ⟨i, j, hij, hi, hj⟩ : ∃ i j : Fin k, i ≠ j ∧ a i = i ∧ a j = j := by
      have : 1 < Fintype.card (Function.fixedPoints a) := by omega
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne⟩ := Fintype.one_lt_card_iff_nontrivial.1 this |>.exists_pair_ne
      exact ⟨i, j, fun h => hne (Subtype.ext h), hi, hj⟩
    refine ⟨g * swap i j, ?_, ?_⟩
    · rw [map_mul, hs, sign_swap hij]
      decide
    · have hc : swap i j * a * (swap i j)⁻¹ = a := by
        have h1 : swap (a i) (a j) = a * swap i j * a⁻¹ := Equiv.swap_apply_apply a i j
        rw [hi, hj] at h1
        have h2 : swap i j * a = a * swap i j := by
          have h3 : swap i j * a = (a * swap i j * a⁻¹) * a := by rw [← h1]
          rw [h3]
          group
        rw [h2, Equiv.swap_inv, mul_assoc, ← Equiv.swap_inv]
        simp
      calc g * swap i j * a * (g * swap i j)⁻¹ = g * (swap i j * a * (swap i j)⁻¹) * g⁻¹ := by
            group
        _ = b := by rw [hc]; exact hg

end PermFacts

section Alt

variable {k : ℕ}

theorem card_le_four_of_alt (hk : k ≤ 7) {E : Subgroup (alternatingGroup (Fin k))}
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  classical
  by_contra hgt
  push Not at hgt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 E := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx2 : (x : alternatingGroup (Fin k)) * x = 1 := hsq x x.2
    have hx2' : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hx2)
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx2') with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨n, hn⟩ := hp2.exists_card_eq
  have hn3 : 3 ≤ n := by
    have h4 : 4 < 2 ^ n := hn ▸ hgt
    by_contra h
    push Not at h
    interval_cases n <;> norm_num at h4
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2
    (show 2 ^ 3 ∣ Nat.card E from ⟨2 ^ (n - 3), by rw [hn, ← pow_add]; congr 1; omega⟩)
  let φ : E →* Perm (Fin k) := (alternatingGroup (Fin k)).subtype.comp E.subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  let F₀ : Subgroup (Perm (Fin k)) := F.map φ
  have hF₀ : Nat.card F₀ = 8 := by
    rw [← Nat.card_congr (F.equivMapOfInjective φ hφ).toEquiv]
    simpa using hF
  have hF₀sq : ∀ g ∈ F₀, g ^ 2 = 1 ∧ sign g = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    have hff : f * f = 1 := Subtype.ext (hsq (f : alternatingGroup (Fin k)) f.2)
    refine ⟨?_, ?_⟩
    · rw [← map_pow, pow_two, hff, map_one]
    · exact (Equiv.Perm.mem_alternatingGroup.1 (f : alternatingGroup (Fin k)).2)
  have hk4 : 4 ≤ k := by
    have hex : ∃ g ∈ F₀, g ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : F₀ = ⊥ := (Subgroup.eq_bot_iff_forall F₀).2 hno
      rw [hbot, Subgroup.card_bot] at hF₀
      omega
    obtain ⟨g, hg, hg1⟩ := hex
    have h4 := card_support_of_even_involution hk (hF₀sq g hg).1 hg1 (hF₀sq g hg).2
    have hle : g.support.card ≤ k := by simpa using Finset.card_le_univ g.support
    omega
  have : Fintype F₀ := Fintype.ofFinite _
  have hcardF₀ : Fintype.card F₀ = 8 := by rw [← Nat.card_eq_fintype_card]; exact hF₀
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group F₀ (Fin k)
  have hfix1 : Fintype.card (MulAction.fixedBy (Fin k) (1 : F₀)) = k := by
    rw [← Nat.card_eq_fintype_card, MulAction.fixedBy_one_eq_univ]
    simp
  have hfixg : ∀ g : F₀, g ≠ 1 → Fintype.card (MulAction.fixedBy (Fin k) g) = k - 4 := by
    intro g hg1
    have hg1' : (g : Perm (Fin k)) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hcard := card_fixedPoints_of_even_involution hk (hF₀sq g g.2).1 hg1' (hF₀sq g g.2).2
    have hset : (MulAction.fixedBy (Fin k) g : Set (Fin k)) =
        Function.fixedPoints (g : Perm (Fin k)) := by
      ext x
      simp [MulAction.mem_fixedBy, Function.fixedPoints, Function.IsFixedPt, Subgroup.smul_def,
        Equiv.Perm.smul_def]
    rw [← hcard, ← Nat.card_eq_fintype_card, hset, Nat.card_eq_fintype_card]
  have hsum : ∑ g : F₀, Fintype.card (MulAction.fixedBy (Fin k) g) = k + 7 * (k - 4) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : F₀)), hfix1,
      Finset.sum_congr rfl (fun g hg => hfixg g (Finset.ne_of_mem_erase hg)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardF₀]
    simp
  rw [hsum, hcardF₀] at hB
  omega

end Alt

end CFSG.CGT.T75I
