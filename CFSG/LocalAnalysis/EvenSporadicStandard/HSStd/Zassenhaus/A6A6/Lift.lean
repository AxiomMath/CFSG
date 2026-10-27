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

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

variable {G : Type*} [Group G]

def liftStab (N : Subgroup G) [N.Normal] (y : G) : Subgroup G where
  carrier := {b | y⁻¹ * (b * y * b⁻¹) ∈ N}
  one_mem' := by simp
  mul_mem' := by
    intro b₁ b₂ hb₁ hb₂
    have h2 : b₁ * (y⁻¹ * (b₂ * y * b₂⁻¹)) * b₁⁻¹ ∈ N := ‹N.Normal›.conj_mem _ hb₂ b₁
    have e : y⁻¹ * (b₁ * b₂ * y * (b₁ * b₂)⁻¹) =
        (y⁻¹ * (b₁ * y * b₁⁻¹)) * (b₁ * (y⁻¹ * (b₂ * y * b₂⁻¹)) * b₁⁻¹) := by group
    show y⁻¹ * (b₁ * b₂ * y * (b₁ * b₂)⁻¹) ∈ N
    rw [e]
    exact N.mul_mem hb₁ h2
  inv_mem' := by
    intro b hb
    have h2 : b⁻¹ * (y⁻¹ * (b * y * b⁻¹)) * b⁻¹⁻¹ ∈ N := ‹N.Normal›.conj_mem _ hb b⁻¹
    have e : y⁻¹ * (b⁻¹ * y * b⁻¹⁻¹) = (b⁻¹ * (y⁻¹ * (b * y * b⁻¹)) * b⁻¹⁻¹)⁻¹ := by group
    show y⁻¹ * (b⁻¹ * y * b⁻¹⁻¹) ∈ N
    rw [e]
    exact N.inv_mem h2

theorem exists_mul_comm_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N) {a : G} {k : ℕ} (ha : a ^ (p ^ k) = 1)
    {y : G} (hy : y⁻¹ * (a * y * a⁻¹) ∈ N) : ∃ n ∈ N, a * (y * n) = (y * n) * a := by
  have hB : Subgroup.zpowers a ≤ liftStab N y := Subgroup.zpowers_le.mpr hy
  have hact : ∀ b ∈ Subgroup.zpowers a, ∀ o ∈ N, y⁻¹ * (b * (y * o) * b⁻¹) ∈ N := by
    intro b hb o ho
    have hbl : y⁻¹ * (b * y * b⁻¹) ∈ N := hB hb
    have e : y⁻¹ * (b * (y * o) * b⁻¹) = (y⁻¹ * (b * y * b⁻¹)) * (b * o * b⁻¹) := by group
    rw [e]
    exact N.mul_mem hbl (‹N.Normal›.conj_mem o ho b)
  let : MulAction ↥(Subgroup.zpowers a) ↥N :=
    { smul := fun b o => ⟨y⁻¹ * ((b : G) * (y * (o : G)) * (b : G)⁻¹), hact b b.2 o o.2⟩
      one_smul := fun o => Subtype.ext (by
        change y⁻¹ * ((1 : G) * (y * (o : G)) * (1 : G)⁻¹) = (o : G)
        group)
      mul_smul := fun b₁ b₂ o => Subtype.ext (by
        change y⁻¹ * (((b₁ : G) * (b₂ : G)) * (y * (o : G)) * ((b₁ : G) * (b₂ : G))⁻¹) =
          y⁻¹ * ((b₁ : G) * (y * (y⁻¹ * ((b₂ : G) * (y * (o : G)) * (b₂ : G)⁻¹))) *
            (b₁ : G)⁻¹)
        group) }
  have hp : IsPGroup p (Subgroup.zpowers a) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ha
  obtain ⟨o₀, ho₀⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card ↥N hN
  refine ⟨o₀, o₀.2, ?_⟩
  have h1 : y⁻¹ * (a * (y * (o₀ : G)) * a⁻¹) = (o₀ : G) :=
    congrArg Subtype.val (ho₀ ⟨a, Subgroup.mem_zpowers a⟩)
  calc a * (y * (o₀ : G)) = y * (y⁻¹ * (a * (y * (o₀ : G)) * a⁻¹)) * a := by group
    _ = y * (o₀ : G) * a := by rw [h1]

theorem exists_pow_lift_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N) (y : G)
    (hy : orderOf (QuotientGroup.mk y : G ⧸ N) = p) :
    ∃ m : ℕ, (QuotientGroup.mk (y ^ m) : G ⧸ N) = QuotientGroup.mk y ∧ orderOf (y ^ m) = p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hdvd : p ∣ orderOf y := hy ▸ orderOf_map_dvd (QuotientGroup.mk' N) y
  obtain ⟨s, hs⟩ := hdvd
  have hypN : y ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hy]
    exact pow_orderOf_eq_one _
  have hord : orderOf (y ^ p) = s := by
    rw [orderOf_pow_of_dvd hp0 ⟨s, hs⟩, hs, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp0)]
  have hsN : s ∣ Nat.card N := by
    rw [← hord]
    have := orderOf_dvd_natCard (⟨y ^ p, hypN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime s p := by
    refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr ?_))
    exact fun h => hN (h.trans hsN)
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact orderOf_pos y |>.ne' (by simpa using hs)
  have hmod : t * s ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [mul_comm, ht, Nat.mod_eq_of_lt hp]
  have htp : Nat.Coprime p t := (Nat.coprime_of_mul_modEq_one s hmod).symm
  have hq : t * s = p * (s * t / p) + 1 := by
    have := Nat.div_add_mod (s * t) p
    rw [ht] at this
    linarith [mul_comm t s]
  refine ⟨t * s, ?_, ?_⟩
  · rw [QuotientGroup.eq, hq, pow_succ, pow_mul]
    have e : (((y ^ p) ^ (s * t / p)) * y)⁻¹ * y = ((y ^ p) ^ (s * t / p))⁻¹ := by group
    rw [e]
    exact N.inv_mem (N.pow_mem hypN _)
  · rw [orderOf_pow, hs, Nat.gcd_mul_right, htp, one_mul,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]

theorem exists_odd_pow_two_power {G : Type*} [Group G] [Finite G] (x : G) :
    ∃ m : ℕ, Odd m ∧ ∃ k : ℕ, (x ^ m) ^ (2 ^ k) = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨m, hm, k, ?_⟩
  rw [← pow_mul, mul_comm, ← hkm]
  exact pow_orderOf_eq_one x

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
