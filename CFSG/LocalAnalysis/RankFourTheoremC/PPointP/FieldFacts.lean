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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Finset

section ZMod

variable {p : ℕ} [hp : Fact p.Prime]

theorem pow_half_zmod (hp2 : p ≠ 2) {a : ZMod p} (n : ℕ) :
    a ^ ((p ^ n - 1) / 2) = (a ^ ((p - 1) / 2)) ^ n := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  induction n with
  | zero => simp
  | succ n ih =>
    have hpn : Odd (p ^ n) := hodd.pow
    obtain ⟨s, hs⟩ := hodd
    obtain ⟨t, ht⟩ := hpn
    have htt : (p ^ n - 1) / 2 = t := by omega
    have hss : (p - 1) / 2 = s := by omega
    have h : p ^ n * p = 2 * (t * p + s) + 1 := by
      calc p ^ n * p = (2 * t + 1) * p := by rw [ht]
        _ = 2 * (t * p) + p := by ring
        _ = 2 * (t * p + s) + 1 := by omega
    have hexp : (p ^ (n + 1) - 1) / 2 = t * p + s := by
      rw [pow_succ, h]
      simp
    rw [hexp, pow_add, pow_mul, ← htt, ih, ← hss, ZMod.pow_card, pow_succ]

end ZMod

variable {F : Type} [Field F] {p n : ℕ}

theorem ringChar_ne_two [CharP F p] (hp2 : p ≠ 2) : ringChar F ≠ 2 := by
  rw [ringChar.eq F p]
  exact hp2

theorem natCast_pow_half [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (m : ℕ) :
    ((m : F)) ^ (p ^ n / 2) =
      (ZMod.castHom (dvd_refl p) F ((m : ZMod p) ^ ((p - 1) / 2))) ^ n := by
  have hodd : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨t, ht⟩ := hodd
  have h1 : p ^ n / 2 = (p ^ n - 1) / 2 := by omega
  have hm : (m : F) = ZMod.castHom (dvd_refl p) F (m : ZMod p) := by simp
  rw [h1, hm, ← map_pow, pow_half_zmod hp2 n, map_pow]


theorem isSquare_natCast_of_even [hp : Fact p.Prime] [CharP F p] [Finite F]
    (hF : Nat.card F = p ^ n) (hp2 : p ≠ 2) (hn : Even n) (m : ℕ) : IsSquare (m : F) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype F
  by_cases hm : (m : F) = 0
  · rw [hm]
    exact IsSquare.zero
  rw [FiniteField.isSquare_iff (ringChar_ne_two hp2) hm]
  have hcard : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [hcard, natCast_pow_half hp2 m]
  have ha : (m : ZMod p) ≠ 0 := by
    intro h
    apply hm
    have : (m : F) = ZMod.castHom (dvd_refl p) F (m : ZMod p) := by simp
    rw [this, h, map_zero]
  have hE2 : ((m : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    have hodd : Odd p := hp.out.odd_of_ne_two hp2
    obtain ⟨s, hs⟩ := hodd
    have : (p - 1) / 2 * 2 = p - 1 := by omega
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one ha
  obtain ⟨k, hk⟩ := hn
  rw [hk, ← two_mul, pow_mul, ← map_pow, hE2, map_one, one_pow]

theorem exists_natCast_not_isSquare [hp : Fact p.Prime] [CharP F p] [Finite F]
    (hF : Nat.card F = p ^ n) (hp2 : p ≠ 2) (hn : Odd n) : ∃ m : ℕ, ¬ IsSquare (m : F) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype F
  have hring : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  obtain ⟨a₀, ha₀⟩ := FiniteField.exists_nonsquare hring
  have ha0 : a₀ ≠ 0 := by
    rintro rfl
    exact ha₀ IsSquare.zero
  refine ⟨a₀.val, fun hsq => ?_⟩
  have hm : ((a₀.val : ℕ) : ZMod p) = a₀ := ZMod.natCast_zmod_val a₀
  have hmF : ((a₀.val : ℕ) : F) = ZMod.castHom (dvd_refl p) F a₀ := by
    rw [← hm]
    simp
  have hne : ((a₀.val : ℕ) : F) ≠ 0 := by
    rw [hmF]
    exact (map_ne_zero (ZMod.castHom (dvd_refl p) F)).mpr ha0
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hE2 : (a₀ ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    obtain ⟨s, hs⟩ := hodd
    have : (p - 1) / 2 * 2 = p - 1 := by omega
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one ha0
  have hE1 : a₀ ^ ((p - 1) / 2) ≠ 1 := by
    intro h1
    apply ha₀
    rw [FiniteField.isSquare_iff hring ha0, ZMod.card]
    obtain ⟨s, hs⟩ := hodd
    have : p / 2 = (p - 1) / 2 := by omega
    rw [this]
    exact h1
  have hEm : a₀ ^ ((p - 1) / 2) = -1 := by
    have := eq_or_eq_neg_of_sq_eq_sq (a₀ ^ ((p - 1) / 2)) 1 (by rw [one_pow]; exact hE2)
    exact this.resolve_left hE1
  rw [FiniteField.isSquare_iff (ringChar_ne_two hp2) hne] at hsq
  have hcard : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [hcard, natCast_pow_half hp2 ((a₀.val : ℕ)), hm, hEm] at hsq
  have hneg : ZMod.castHom (dvd_refl p) F (-1) = -1 :=
    ((ZMod.castHom (dvd_refl p) F).map_neg 1).trans (by rw [map_one])
  rw [hneg, hn.neg_one_pow] at hsq
  exact ringChar_ne_two hp2 (neg_one_eq_one_iff.mp hsq)


theorem isSquare_or_isSquare_mul [Finite F] {ν s : F} (hν : ¬ IsSquare ν) (hs : s ≠ 0) :
    IsSquare s ∨ IsSquare (s * ν) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype F
  by_cases h : IsSquare s
  · exact Or.inl h
  right
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hν IsSquare.zero
  have h1 : quadraticChar F s = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h
  have h2 : quadraticChar F ν = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hν
  have h3 : quadraticChar F (s * ν) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero hs hν0)).mp h3

theorem exists_not_natCast [hp : Fact p.Prime] [CharP F p] [Finite F] (hF : Nat.card F = p ^ n)
    (hn : 2 ≤ n) : ∃ c : F, ∀ m : ℕ, c ≠ (m : F) := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) F) := by
    intro c
    obtain ⟨m, hm⟩ := h c
    refine ⟨(m : ZMod p), ?_⟩
    rw [hm]
    simp
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) F) :=
    ⟨RingHom.injective _, hsurj⟩
  have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hF, Nat.card_zmod] at hc
  have hp1 : p ^ n = p ^ 1 := by rw [pow_one]; exact hc.symm
  have := Nat.pow_right_injective hp.out.two_le hp1
  omega

theorem exists_square_line [hp : Fact p.Prime] [CharP F p] [Finite F] (hF : Nat.card F = p ^ n)
    (hp2 : p ≠ 2) (hn : Even n) (h4 : 4 ≤ n) :
    ∃ c : F, (∀ m : ℕ, c ≠ (m : F)) ∧ ∀ m : ℕ, IsSquare ((m : F) + c) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype F
  obtain ⟨k, hk⟩ := hn
  have hk2 : 2 ≤ k := by omega
  have _alg : Algebra (ZMod p) F := ZMod.algebra F p
  have hfinF : Module.finrank (ZMod p) F = n := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)
    rw [hF, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hp.out.two_le this).symm
  have hfinK : Module.finrank (ZMod p) (GaloisField p k) = k := GaloisField.finrank p (by omega)
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
    (K := GaloisField p k) (L := F) (by rw [hfinK, hfinF, hk]; exact ⟨2, by ring⟩)
  have hKcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by omega)
  obtain ⟨c₀, hc₀⟩ := exists_not_natCast (F := GaloisField p k) hKcard hk2
  have hinj : Function.Injective ι := RingHom.injective (ι : GaloisField p k →+* F)
  refine ⟨ι c₀, fun m h => hc₀ m ?_, fun m => ?_⟩
  · exact hinj (by rw [h, map_natCast])
  have hp0 : ((p : ℕ) : GaloisField p k) = 0 := CharP.cast_eq_zero _ p
  have hd : ((m : GaloisField p k) + c₀) ≠ 0 := by
    intro h0
    apply hc₀ ((p - 1) * m)
    have h1 : c₀ = -(m : GaloisField p k) := by linear_combination h0
    rw [h1, Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one, hp0, zero_sub, neg_one_mul]
  have hmc : (m : F) + ι c₀ = ι ((m : GaloisField p k) + c₀) := by
    rw [map_add, map_natCast]
  rw [hmc]
  have hne : ι ((m : GaloisField p k) + c₀) ≠ 0 := by
    exact (map_ne_zero ι).mpr hd
  rw [FiniteField.isSquare_iff (ringChar_ne_two hp2) hne]
  obtain ⟨_⟩ := nonempty_fintype (GaloisField p k)
  have hKc : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hFc : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hd1 := FiniteField.pow_card_sub_one_eq_one ((m : GaloisField p k) + c₀) hd
  rw [hKc] at hd1
  have hodd : Odd (p ^ k) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨u, hu⟩ := hodd
  have hw : p ^ n = 2 * (2 * (u * (u + 1))) + 1 := by
    have : p ^ n = p ^ k * p ^ k := by rw [hk, pow_add]
    rw [this, hu]
    ring
  have hexp : Fintype.card F / 2 = (p ^ k - 1) * (u + 1) := by
    rw [hFc, hw]
    have h1 : p ^ k - 1 = 2 * u := by omega
    rw [h1]
    have h2 : 2 * u * (u + 1) = 2 * (u * (u + 1)) := by ring
    rw [h2]
    omega
  rw [hexp, pow_mul, ← map_pow, hd1, map_one, one_pow]


@[expose] def squareSet (F : Type) [Field F] : Set F := {t | ∃ a : F, a ≠ 0 ∧ t = a ^ 2}

theorem ncard_squareSet [hp : Fact p.Prime] [CharP F p] [Finite F] (hF : Nat.card F = p ^ n)
    (hp2 : p ≠ 2) : (squareSet F).ncard = (p ^ n - 1) / 2 := by
  classical
  obtain ⟨_⟩ := nonempty_fintype F
  have h0 : squareSet F = ((Finset.univ.image fun a : Fˣ => ((a : F)) ^ 2 : Finset F) : Set F) := by
    ext t
    simp only [squareSet, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Units.mk0 a ha, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.ne_zero, rfl⟩
  have h1 : (Finset.univ.image fun a : Fˣ => ((a : F)) ^ 2) =
      (Finset.univ.image fun a : Fˣ => a ^ 2).image Units.val := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a ^ 2, ⟨a, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp⟩
  rw [h0, Set.ncard_coe_finset, h1, Finset.card_image_of_injective _ Units.val_injective]
  have h2 : ((Finset.univ.image fun a : Fˣ => a ^ 2 : Finset Fˣ) : Set Fˣ) =
      ((powMonoidHom 2 : Fˣ →* Fˣ).range : Set Fˣ) := by
    ext a
    simp
  have h3 : (Finset.univ.image fun a : Fˣ => a ^ 2).card =
      Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range := by
    rw [← Set.ncard_coe_finset, h2, ← Nat.card_coe_set_eq]
    rfl
  rw [h3]
  have h4 := Subgroup.index_mul_card (powMonoidHom 2 : Fˣ →* Fˣ).range
  rw [IsCyclic.index_powMonoidHom_range, Nat.card_units, hF] at h4
  have hodd : Odd (p ^ n) := (hp.out.odd_of_ne_two hp2).pow
  obtain ⟨t, ht⟩ := hodd
  have h5 : (p ^ n - 1).gcd 2 = 2 := Nat.gcd_eq_right ⟨t, by omega⟩
  rw [h5] at h4
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
