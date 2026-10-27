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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

theorem card_modEq_five_fixed {α : Type*} [Finite α] (f : α → α) (hf : ∀ a, f^[5] a = a) :
    Nat.card α ≡ (Function.fixedPoints f).ncard [MOD 5] := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let F : Function.End α := f
  have hF : F ^ 5 ^ 1 = 1 := by
    funext a
    exact hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := 5) (n := 1) hF
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  rw [← Nat.card_coe_set_eq]
  exact h

section Aut

variable {Λ : Type*} [Group Λ]

@[expose] def fixSub (P : Subgroup (MulAut Λ)) : Subgroup Λ where
  carrier := {l | ∀ p ∈ P, p l = l}
  one_mem' := fun p _ => map_one p
  mul_mem' := fun {a b} ha hb p hp => by rw [map_mul, ha p hp, hb p hp]
  inv_mem' := fun {a} ha p hp => by rw [map_inv, ha p hp]

theorem aut_trivial_of_fpf [Finite Λ] (hcard : Nat.card Λ = 16) {P : Subgroup (MulAut Λ)}
    (hP : IsPGroup 2 P) {x : MulAut Λ} (hx5 : x ^ 5 = 1) (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hfpf : ∀ l : Λ, x l = l → l = 1) : P = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxpow : ∀ n : ℕ, ∀ p ∈ P, x ^ n * p * (x ^ n)⁻¹ ∈ P := by
    intro n
    induction n with
    | zero => intro p hp; simpa using hp
    | succ n ih =>
      intro p hp
      have := hxP _ (ih p hp)
      have e : x * (x ^ n * p * (x ^ n)⁻¹) * x⁻¹ = x ^ (n + 1) * p * (x ^ (n + 1))⁻¹ := by group
      rwa [e] at this
  have hxinv : ∀ p ∈ P, x⁻¹ * p * x ∈ P := by
    intro p hp
    have h4 : x⁻¹ = x ^ 4 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ']
      exact hx5
    have := hxpow 4 p hp
    rwa [← h4, inv_inv] at this
  have hFne : fixSub P ≠ ⊥ := by
    have hdvd : 2 ∣ Nat.card Λ := by rw [hcard]; norm_num
    have h1 : (1 : Λ) ∈ MulAction.fixedPoints P Λ := by
      rw [MulAction.mem_fixedPoints]
      intro p
      exact map_one (p : MulAut Λ)
    obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point Λ hdvd h1
    rw [MulAction.mem_fixedPoints] at hb
    intro hbot
    apply hb1
    have hbF : b ∈ fixSub P := fun p hp => hb ⟨p, hp⟩
    rw [hbot, Subgroup.mem_bot] at hbF
    exact hbF.symm
  have hxF : ∀ l ∈ fixSub P, x l ∈ fixSub P := by
    intro l hl p hp
    have h1 : (x⁻¹ * p * x) l = l := hl _ (hxinv p hp)
    calc p (x l) = (x * (x⁻¹ * p * x)) l := by simp [mul_assoc]
      _ = x ((x⁻¹ * p * x) l) := rfl
      _ = x l := by rw [h1]
  let f : ↥(fixSub P) → ↥(fixSub P) := fun l => ⟨x l.1, hxF l.1 l.2⟩
  have hf : ∀ n : ℕ, ∀ a : ↥(fixSub P), ((f^[n] a : ↥(fixSub P)) : Λ) = (x ^ n) a.1 := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', pow_succ']
      change x ((f^[n] a : ↥(fixSub P)) : Λ) = (x * x ^ n) a.1
      rw [ih]
      rfl
  have hf5 : ∀ a, f^[5] a = a := by
    intro a
    apply Subtype.ext
    rw [hf, hx5]
    rfl
  have hmod := card_modEq_five_fixed f hf5
  have hfix : Function.fixedPoints f = {1} := by
    ext a
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_singleton_iff]
    constructor
    · intro h
      apply Subtype.ext
      have := hfpf a.1 (congrArg Subtype.val h)
      exact this
    · intro h
      rw [h]
      apply Subtype.ext
      exact map_one x
  rw [hfix, Set.ncard_singleton] at hmod
  have hdvd16 : Nat.card (fixSub P) ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card (fixSub P)
    rw [hcard] at this
    simpa using this
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd16
  rw [hk] at hmod
  have hk' : k = 0 ∨ k = 4 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  have hcard16 : Nat.card (fixSub P) = 16 := by
    rcases hk' with rfl | rfl
    · exfalso
      apply hFne
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hk]; norm_num)
    · rw [hk]; norm_num
  have hFtop : fixSub P = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcard16, hcard])
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  ext l
  have : l ∈ fixSub P := by rw [hFtop]; exact Subgroup.mem_top l
  rw [MulAut.one_apply]
  exact this p hp

@[expose] def stabSub (N : Subgroup Λ) : Subgroup (MulAut Λ) where
  carrier := {φ | ∀ n, n ∈ N ↔ φ n ∈ N}
  one_mem' := fun n => Iff.rfl
  mul_mem' := fun {φ ψ} hφ hψ n => (hψ n).trans (hφ (ψ n))
  inv_mem' := fun {φ} hφ n => by
    have := hφ (φ⁻¹ n)
    rw [show φ (φ⁻¹ n) = n by simp] at this
    exact this.symm

theorem mem_stabSub {N : Subgroup Λ} {φ : MulAut Λ} : φ ∈ stabSub N ↔ ∀ n, n ∈ N ↔ φ n ∈ N := Iff.rfl

theorem map_eq_of_mem_stabSub {N : Subgroup Λ} {φ : MulAut Λ} (h : φ ∈ stabSub N) :
    N.map (φ : MulAut Λ).toMonoidHom = N := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact (h n).1 hn
  · intro hy
    refine ⟨φ⁻¹ y, ?_, by simp⟩
    rw [h (φ⁻¹ y)]
    simpa using hy

@[expose] def quotAutHom (N : Subgroup Λ) [N.Normal] : stabSub N →* MulAut (Λ ⧸ N) where
  toFun φ := QuotientGroup.congr N N (φ : MulAut Λ) (map_eq_of_mem_stabSub φ.2)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H l => rfl
  map_mul' φ ψ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H l => rfl

theorem layer_trivial [Finite Λ] (hcomm : ∀ a b : Λ, a * b = b * a) {N : Subgroup Λ}
    (hidx : N.index = 16) {P : Subgroup (MulAut Λ)} (hP : IsPGroup 2 P) {x : MulAut Λ}
    (hx5 : x ^ 5 = 1) (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hPN : ∀ p ∈ P, ∀ n, n ∈ N ↔ p n ∈ N)
    (hxN : ∀ n, n ∈ N ↔ x n ∈ N) (hfpf : ∀ l : Λ, x l * l⁻¹ ∈ N → l ∈ N) :
    ∀ p ∈ P, ∀ l : Λ, p l * l⁻¹ ∈ N := by
  classical
  haveI hN : N.Normal := ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hPS : P ≤ stabSub N := fun p hp => hPN p hp
  have hxS : x ∈ stabSub N := hxN
  have hcardL : Nat.card (Λ ⧸ N) = 16 := by rw [← Subgroup.index_eq_card]; exact hidx
  let S := stabSub N
  let ρ := quotAutHom N
  have hPsub : IsPGroup 2 (P.subgroupOf S) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  have hP' : IsPGroup 2 ↥((P.subgroupOf S).map ρ) := hPsub.map ρ
  let x' : MulAut (Λ ⧸ N) := ρ ⟨x, hxS⟩
  have hx5' : x' ^ 5 = 1 := by
    have : (⟨x, hxS⟩ : S) ^ 5 = 1 := Subtype.ext hx5
    rw [← map_pow, this, map_one]
  have hxP' : ∀ q ∈ (P.subgroupOf S).map ρ, x' * q * x'⁻¹ ∈ (P.subgroupOf S).map ρ := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hq
    refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩ * p * ⟨x, hxS⟩⁻¹, ?_, by simp [x']⟩
    rw [Subgroup.mem_subgroupOf]
    have := hxP (p : MulAut Λ) (Subgroup.mem_subgroupOf.1 hp)
    simpa using this
  have hfpf' : ∀ q : Λ ⧸ N, x' q = q → q = 1 := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H l =>
      have h1 : (QuotientGroup.mk (x l) : Λ ⧸ N) = QuotientGroup.mk l := hq
      have h2 := QuotientGroup.eq.1 h1
      have h3 : x l * l⁻¹ ∈ N := by
        have : (x l)⁻¹ * l = (x l * l⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv, hcomm]
        rw [this] at h2
        exact (Subgroup.inv_mem_iff N).1 h2
      exact (QuotientGroup.eq_one_iff l).2 (hfpf l h3)
  have hbot := aut_trivial_of_fpf hcardL hP' hx5' hxP' hfpf'
  intro p hp l
  have hmem : ρ ⟨p, hPS hp⟩ ∈ (P.subgroupOf S).map ρ :=
    Subgroup.mem_map.2 ⟨⟨p, hPS hp⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun φ : MulAut (Λ ⧸ N) => φ (QuotientGroup.mk l)) hmem
  simp only [MulAut.one_apply] at h1
  have h2 : (QuotientGroup.mk (p l) : Λ ⧸ N) = QuotientGroup.mk l := h1
  have h3 := QuotientGroup.eq.1 h2
  have : (p l)⁻¹ * l = (p l * l⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, hcomm]
  rw [this] at h3
  exact (Subgroup.inv_mem_iff N).1 h3

@[expose] def trivOn [Finite Λ] (B C : Subgroup Λ) (hBC : B ≤ C) : Subgroup (MulAut Λ) where
  carrier := {φ | ∀ c ∈ C, φ c * c⁻¹ ∈ B}
  one_mem' := fun c _ => by simp
  mul_mem' := fun {φ ψ} hφ hψ c hc => by
    have hb := hψ c hc
    have h1 : φ (ψ c * c⁻¹) ∈ B := by
      have h2 := hφ _ (hBC hb)
      have : φ (ψ c * c⁻¹) = (φ (ψ c * c⁻¹) * (ψ c * c⁻¹)⁻¹) * (ψ c * c⁻¹) := by group
      rw [this]
      exact B.mul_mem h2 hb
    have h3 := hφ c hc
    have e : (φ * ψ) c * c⁻¹ = φ (ψ c * c⁻¹) * (φ c * c⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv]
      group
    rw [e]
    exact B.mul_mem h1 h3
  inv_mem' := fun {φ} hφ c hc => by
    have hCmap : ∀ c' ∈ C, φ c' ∈ C := fun c' hc' => by
      have : φ c' = (φ c' * c'⁻¹) * c' := by group
      rw [this]
      exact C.mul_mem (hBC (hφ c' hc')) hc'
    let g : C → C := fun c' => ⟨φ c', hCmap c' c'.2⟩
    have hginj : Function.Injective g := fun a b hab => by
      apply Subtype.ext
      exact φ.injective (congrArg Subtype.val hab)
    obtain ⟨c', hc'⟩ := (Finite.injective_iff_surjective.1 hginj) ⟨c, hc⟩
    have hc'eq : φ c'.1 = c := congrArg Subtype.val hc'
    have hh : φ⁻¹ c = c'.1 := by rw [← hc'eq]; simp
    have h1 := hφ c'.1 c'.2
    rw [hc'eq] at h1
    rw [hh]
    have : c'.1 * c⁻¹ = (c * c'.1⁻¹)⁻¹ := by group
    rw [this]
    exact B.inv_mem h1

theorem mem_trivOn [Finite Λ] {B C : Subgroup Λ} {hBC : B ≤ C} {φ : MulAut Λ} :
    φ ∈ trivOn B C hBC ↔ ∀ c ∈ C, φ c * c⁻¹ ∈ B := Iff.rfl

end Aut

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
