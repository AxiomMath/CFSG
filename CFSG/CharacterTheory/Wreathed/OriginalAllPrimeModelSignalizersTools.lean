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
public import Mathlib.GroupTheory.FixedPointFree
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

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open scoped Pointwise

section Groups

variable {G : Type*} [Group G]

theorem conj_eq_inv_of_inf_centralizer_eq_bot {X : Subgroup G} [Finite X] {t : G}
    (ht : t * t = 1) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hX : X ⊓ Subgroup.centralizer {t} = ⊥) {x : G} (hx : x ∈ X) : t * x * t⁻¹ = x⁻¹ := by
  have hmem : ∀ y ∈ X, t * y * t⁻¹ ∈ X := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp htX y).mp hy
  let φ : X →* X :=
    { toFun := fun y => ⟨t * y * t⁻¹, hmem y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp [mul_assoc] }
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hfree : MonoidHom.FixedPointFree φ := by
    intro y hy
    have hy' : t * (y : G) * t⁻¹ = y := congrArg Subtype.val hy
    have hc : (y : G) ∈ Subgroup.centralizer {t} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * t = t * y * t⁻¹ * t := by rw [hy']
        _ = t * y := by group
    have hyb : (y : G) ∈ X ⊓ Subgroup.centralizer {t} := ⟨y.2, hc⟩
    rw [hX] at hyb
    exact Subtype.ext ((Subgroup.mem_bot).mp hyb)
  have hinv : Function.Involutive φ := by
    intro y
    apply Subtype.ext
    change t * (t * (y : G) * t⁻¹) * t⁻¹ = y
    rw [htinv]
    calc t * (t * (y : G) * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht, one_mul, mul_one]
  have h := congrFun (hfree.coe_eq_inv_of_involutive hinv) ⟨x, hx⟩
  exact congrArg Subtype.val h

theorem le_or_le_of_forall_mem_or_mem {X A B : Subgroup G} (h : ∀ x ∈ X, x ∈ A ∨ x ∈ B) :
    X ≤ A ∨ X ≤ B := by
  by_contra hcon
  rw [not_or, IsConcreteLE.not_le_iff_exists, IsConcreteLE.not_le_iff_exists] at hcon
  obtain ⟨⟨x, hxX, hxA⟩, ⟨y, hyX, hyB⟩⟩ := hcon
  have hxB : x ∈ B := (h x hxX).resolve_left hxA
  have hyA : y ∈ A := (h y hyX).resolve_right hyB
  rcases h (x * y) (X.mul_mem hxX hyX) with hxy | hxy
  · exact hxA (by simpa using A.mul_mem hxy (A.inv_mem hyA))
  · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) hxy)

theorem le_normalizer_of_forall_conj_mem {C R : Subgroup G}
    (h : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R) : C ≤ Subgroup.normalizer (R : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h c hc r, fun hr => ?_⟩
  have h' := h c⁻¹ (C.inv_mem hc) _ hr
  have he : c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r := by group
  rwa [he] at h'

@[expose] def permProduct (H K : Subgroup G) (h : (H : Set G) * K = K * H) : Subgroup G where
  carrier := (H : Set G) * K
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    have hbc : b * c ∈ (K : Set G) * H := ⟨b, hb, c, hc, rfl⟩
    rw [← h] at hbc
    obtain ⟨e, he, f, hf, hef⟩ := hbc
    change e * f = b * c at hef
    refine ⟨a * e, H.mul_mem ha he, f * d, K.mul_mem hf hd, ?_⟩
    calc a * e * (f * d) = a * (e * f) * d := by group
      _ = a * (b * c) * d := by rw [hef]
      _ = a * b * (c * d) := by group
  one_mem' := ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hba : b⁻¹ * a⁻¹ ∈ (K : Set G) * H := ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
    rw [← h] at hba
    simpa [mul_inv_rev] using hba

theorem mem_permProduct {H K : Subgroup G} {h : (H : Set G) * K = K * H} {x : G} :
    x ∈ permProduct H K h ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := Iff.rfl

theorem left_le_permProduct {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    H ≤ permProduct H K h := fun a ha => ⟨a, ha, 1, K.one_mem, mul_one a⟩

theorem right_le_permProduct {H K : Subgroup G} (h : (H : Set G) * K = K * H) :
    K ≤ permProduct H K h := fun b hb => ⟨1, H.one_mem, b, hb, one_mul b⟩

end Groups

section Orbits

theorem dvd_card_of_card_orbit {A X : Type*} [Group A] [MulAction A X] [Finite X] {n : ℕ}
    (h : ∀ x : X, Nat.card (MulAction.orbit A x) = n) : n ∣ Nat.card X := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient A X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits A X), Nat.card_sigma]
  simp only [h, Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

theorem dvd_ncard_of_card_orbit {A X : Type*} [Group A] [MulAction A X] {S : Set X}
    (hS : S.Finite) (hinv : ∀ a : A, ∀ x ∈ S, a • x ∈ S) {n : ℕ}
    (h : ∀ x ∈ S, Nat.card (MulAction.orbit A x) = n) : n ∣ S.ncard := by
  let S' : SubMulAction A X := ⟨S, fun a x hx => hinv a x hx⟩
  have : Finite S' := hS.to_subtype
  have key : ∀ x : S', Nat.card (MulAction.orbit A x) = n := by
    intro x
    rw [← h x x.2]
    refine Nat.card_congr
      { toFun := fun y => ⟨(y : S'), ?_⟩
        invFun := fun y => ⟨⟨y, ?_⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    · obtain ⟨a, ha⟩ := y.2
      exact ⟨a, by rw [← ha]; rfl⟩
    · obtain ⟨a, ha⟩ := y.2
      rw [← ha]
      exact hinv a x x.2
    · obtain ⟨a, ha⟩ := y.2
      exact ⟨a, Subtype.ext ha⟩
  rw [← Nat.card_coe_set_eq]
  exact dvd_card_of_card_orbit (A := A) (X := S') key

end Orbits

section Arithmetic

theorem eq_one_of_dvd_of_eq_one_add {q k j : ℕ} (hq : Odd q) (hq3 : 3 ≤ q)
    (hk : k ∣ q * (q - 1)) (hj : k = 1 + (q + 1) * j) : k = 1 := by
  obtain ⟨n, hn⟩ := hk
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using hj
  exfalso
  subst hj
  obtain ⟨r, hr⟩ := hq
  have hq1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by push_cast [show 1 ≤ q by omega]; ring
  have hnZ : (q : ℤ) * ((q : ℤ) - 1) = (1 + ((q : ℤ) + 1) * j) * n := by
    rw [← hq1]
    exact_mod_cast hn
  have hnpos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp only [Nat.cast_zero, mul_zero] at hnZ
      have : (3 : ℤ) ≤ q := by exact_mod_cast hq3
      nlinarith
    · exact h
  have hd : (n : ℤ) - 2 = ((q : ℤ) + 1) * ((q : ℤ) - 2 - j * n) := by linear_combination -hnZ
  have hjZ : (1 : ℤ) ≤ j := by exact_mod_cast hjpos
  have hnZ1 : (1 : ℤ) ≤ n := by exact_mod_cast hnpos
  have hq3Z : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  rcases lt_trichotomy ((q : ℤ) - 2 - j * n) 0 with hneg | hzero | hpos
  · have : ((q : ℤ) + 1) * ((q : ℤ) - 2 - j * n) ≤ -((q : ℤ) + 1) := by nlinarith
    nlinarith
  · have hn2 : (n : ℤ) = 2 := by rw [hzero, mul_zero] at hd; linarith
    have hqj : (q : ℤ) = 2 * j + 2 := by rw [hn2] at hzero; linarith
    have hqr : (q : ℤ) = 2 * r + 1 := by exact_mod_cast hr
    omega
  · have hn3 : (q : ℤ) + 3 ≤ n := by nlinarith
    have : (n : ℤ) ≤ j * n := by nlinarith
    nlinarith

end Arithmetic

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
