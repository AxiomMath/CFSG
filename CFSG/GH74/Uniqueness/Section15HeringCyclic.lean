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
public import Mathlib.GroupTheory.Transfer
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

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ} (ha : x ^ a ∈ H)
    (hb : x ^ b ∈ H) (hab : a.Coprime b) : x ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at h
  have : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

theorem conj_pow_eq {n r : G} {k : ℕ} (h : n * r * n⁻¹ = r ^ k) (j : ℕ) :
    n ^ j * r * (n ^ j)⁻¹ = r ^ (k ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, pow_mul, ← ih]
    have : ∀ i : ℕ, (n ^ j * r * (n ^ j)⁻¹) ^ i = n ^ j * r ^ i * (n ^ j)⁻¹ := fun i => by
      rw [conj_pow]
    rw [this, ← h]
    group

theorem mem_normalizer_of_conj_mem [Finite G] {P : Subgroup G} {n : G}
    (h : ∀ x ∈ P, n * x * n⁻¹ ∈ P) : n ∈ normalizer (P : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : P → P := fun y => ⟨n * y * n⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨n * x * n⁻¹, hx⟩
  have hyx : (y : G) = x := by
    have := congrArg Subtype.val hy
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact this
  exact hyx ▸ y.2

theorem normalizer_le_centralizer_of_cyclic [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (R : Sylow p G) {r : G} (hr : (R : Subgroup G) = zpowers r) {b : ℕ}
    (hb : orderOf r = p ^ (b + 1))
    (hNC : normalizer ((zpowers (r ^ p ^ b) : Subgroup G) : Set G) ≤
      centralizer ((zpowers (r ^ p ^ b) : Subgroup G) : Set G)) :
    normalizer ((R : Subgroup G) : Set G) ≤ centralizer ((R : Subgroup G) : Set G) := by
  have hcR : ∀ c : G, c * r = r * c → c ∈ centralizer ((R : Subgroup G) : Set G) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, hr] at hy
    obtain ⟨i, rfl⟩ := hy
    show r ^ i * c = c * r ^ i
    exact (Commute.zpow_left (hc.symm : Commute r c) i).eq
  have key : ∀ n ∈ normalizer ((R : Subgroup G) : Set G),
      n ^ p ^ b ∈ centralizer ((R : Subgroup G) : Set G) := by
    intro n hn
    have hnr : n * r * n⁻¹ ∈ (R : Subgroup G) :=
      (mem_normalizer_iff.mp hn r).mp (hr ▸ mem_zpowers r)
    rw [hr] at hnr
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hnr)
    simp only at hk
    have hnP : n ∈ normalizer ((zpowers (r ^ p ^ b) : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conj_mem
      rintro x ⟨i, rfl⟩
      refine ⟨k * i, ?_⟩
      simp only
      rw [← conj_zpow, ← conj_pow, ← hk, zpow_mul, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
    have hnc := hNC hnP
    rw [mem_centralizer_iff] at hnc
    have h1 := hnc (r ^ p ^ b) (mem_zpowers _)
    have h2 : (n * r * n⁻¹) ^ p ^ b = r ^ p ^ b := by
      rw [conj_pow, ← h1]
      group
    rw [← hk, ← pow_mul] at h2
    have h3 : p ^ b * k ≡ p ^ b * 1 [MOD p ^ b * p] := by
      rw [mul_one, mul_comm (p ^ b) k, ← pow_succ, ← hb]
      exact pow_eq_pow_iff_modEq.mp h2
    have h4 : k ≡ 1 [MOD p] := Nat.ModEq.mul_left_cancel' (pow_ne_zero b hp.out.ne_zero) h3
    have h5 : ((p : ℤ) ^ (b + 1)) ∣ (k : ℤ) ^ p ^ b - 1 ^ p ^ b := by
      apply dvd_sub_pow_of_dvd_sub
      have := (Nat.modEq_iff_dvd.mp h4.symm)
      simpa using this
    have h6 : 1 ≡ k ^ p ^ b [MOD p ^ (b + 1)] := by
      rw [Nat.modEq_iff_dvd]
      push_cast
      simpa using h5
    have h7 : r ^ (k ^ p ^ b) = r := by
      rw [pow_eq_pow_of_modEq h6.symm (hb ▸ pow_orderOf_eq_one r), pow_one]
    apply hcR
    have h8 := conj_pow_eq hk.symm (p ^ b)
    rw [h7] at h8
    calc n ^ p ^ b * r = n ^ p ^ b * r * (n ^ p ^ b)⁻¹ * n ^ p ^ b := by group
      _ = r * n ^ p ^ b := by rw [h8]
  intro n hn
  obtain ⟨c, j', hj', hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' p
    hp.out.ne_one
  have hcop : j'.Coprime p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hj')
  have hn₂ : n ^ p ^ c ∈ centralizer ((R : Subgroup G) : Set G) := by
    apply mem_of_pow_mem_of_coprime (a := p ^ b) (b := j')
    · exact key _ ((normalizer _).pow_mem hn _)
    · rw [← pow_mul, ← hord, pow_orderOf_eq_one]
      exact one_mem _
    · exact Nat.Coprime.pow_left b (Nat.coprime_comm.mp hcop)
  have hn₁ : n ^ j' ∈ (R : Subgroup G) := by
    have hp1 : IsPGroup p (zpowers (n ^ j')) := by
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
      refine ⟨c, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm,
        ← hord, pow_orderOf_eq_one, one_zpow]
    have hle : zpowers (n ^ j') ≤ normalizer ((R : Subgroup G) : Set G) :=
      (zpowers_le (H := normalizer _)).mpr ((normalizer _).pow_mem hn _)
    have hsup := IsPGroup.to_sup_of_normal_left' R.isPGroup' hp1 hle
    have hmax := R.is_maximal' hsup le_sup_left
    rw [← hmax]
    exact mem_sup_right (mem_zpowers _)
  have hn₁C : n ^ j' ∈ centralizer ((R : Subgroup G) : Set G) := by
    rw [hr] at hn₁
    obtain ⟨i, hi⟩ := hn₁
    apply hcR
    rw [← hi]
    exact (Commute.zpow_left (Commute.refl r) i).eq
  exact mem_of_pow_mem_of_coprime hn₁C hn₂ (Nat.Coprime.pow_right c hcop)

theorem exists_normal_pComplement_of_cyclic [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (R : Sylow p G) {r : G} (hr : (R : Subgroup G) = zpowers r) {b : ℕ}
    (hb : orderOf r = p ^ (b + 1))
    (hNC : normalizer ((zpowers (r ^ p ^ b) : Subgroup G) : Set G) ≤
      centralizer ((zpowers (r ^ p ^ b) : Subgroup G) : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ ¬ p ∣ Nat.card N ∧ N.index = Nat.card R := by
  have hNR := normalizer_le_centralizer_of_cyclic R hr hb hNC
  exact ⟨(MonoidHom.transferSylow R hNR).ker, inferInstance,
    MonoidHom.not_dvd_card_ker_transferSylow R hNR,
    (MonoidHom.ker_transferSylow_isComplement' R hNR).symm.index_eq_card⟩

end CFSG.GH74.Uniqueness.Hering
