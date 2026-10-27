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

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open Subgroup

section Abstract

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem eq_one_of_mem_odd {O : Subgroup Γ} (hO : Odd (Nat.card O)) {o : Γ} (ho : o ∈ O) {k : ℕ}
    (hk : o ^ 2 ^ k = 1) : o = 1 := by
  have h1 : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho
  have h2 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hc : Nat.Coprime (2 ^ k) (Nat.card O) := (Nat.coprime_two_left.mpr hO).pow_left k
  have h3 : orderOf o ∣ 1 := hc ▸ Nat.dvd_gcd h2 h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem exists_mul_normalizer {E O : Subgroup Γ} [O.Normal] [(E ⊔ O).Normal]
    (hO : Odd (Nat.card O)) (hE : IsPGroup 2 E) (c : Γ) :
    ∃ o ∈ O, ∃ n ∈ Subgroup.normalizer (E : Set Γ), c = o * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Γ := E ⊔ O with hN
  have hEN : E ≤ N := le_sup_left
  let P : Sylow 2 ↥N :=
    { toSubgroup := E.subgroupOf N
      isPGroup' := hE.comap_subtype
      is_maximal' := by
        intro Q hQ hEQ
        refine le_antisymm (fun x hx => ?_) hEQ
        have hxN : (x : Γ) ∈ O ⊔ E := by rw [sup_comm]; exact x.2
        obtain ⟨o, ho, e, he, hoe⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
        have heQ : (⟨e, hEN he⟩ : ↥N) ∈ Q := hEQ (Subgroup.mem_subgroupOf.mpr he)
        have hoQ : (⟨o, Subgroup.mem_sup_right ho⟩ : ↥N) ∈ Q := by
          have h1 := Q.mul_mem hx (Q.inv_mem heQ)
          have e1 : x * (⟨e, hEN he⟩ : ↥N)⁻¹ = ⟨o, Subgroup.mem_sup_right ho⟩ := by
            apply Subtype.ext
            show (x : Γ) * e⁻¹ = o
            rw [← hoe]
            group
          rwa [e1] at h1
        obtain ⟨k, hk⟩ := hQ ⟨_, hoQ⟩
        have hk' : o ^ 2 ^ k = 1 := congrArg (fun z : ↥N => (z : Γ)) (congrArg Subtype.val hk)
        have ho1 : o = 1 := eq_one_of_mem_odd hO ho hk'
        rw [Subgroup.mem_subgroupOf]
        have : (x : Γ) = e := by rw [← hoe, ho1, one_mul]
        rw [this]
        exact he }
  have hF := Sylow.normalizer_sup_eq_top P
  have hP : (P : Subgroup ↥N).map N.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEN
  rw [hP] at hF
  have hc : c ∈ Subgroup.normalizer (E : Set Γ) ⊔ N := by rw [hF]; exact Subgroup.mem_top c
  obtain ⟨n, hn, h, hh, hnh⟩ := Subgroup.mem_sup_of_normal_right.mp hc
  have hh' : h ∈ O ⊔ E := by rw [sup_comm]; exact hh
  obtain ⟨o, ho, e, he, hoe⟩ := Subgroup.mem_sup_of_normal_left.mp hh'
  refine ⟨n * o * n⁻¹, Normal.conj_mem inferInstance o ho n, n * e, ?_, ?_⟩
  · exact Subgroup.mul_mem _ hn (Subgroup.le_normalizer he)
  · rw [← hnh, ← hoe]
    group

end Abstract

section Ambient

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_mul_normalizer_of_le {C E O : Subgroup Y} (hEC : E ≤ C) (hOC : O ≤ C)
    (hOn : ∀ c ∈ C, ∀ x ∈ O, c * x * c⁻¹ ∈ O)
    (hEO : ∀ c ∈ C, ∀ x ∈ E, c * x * c⁻¹ ∈ E ⊔ O) (hO : Odd (Nat.card O)) (hE : IsPGroup 2 E)
    {c : Y} (hc : c ∈ C) :
    ∃ o ∈ O, ∃ n ∈ C, n ∈ Subgroup.normalizer (E : Set Y) ∧ c = o * n := by
  have hN : ∀ c ∈ C, ∀ x ∈ E ⊔ O, c * x * c⁻¹ ∈ E ⊔ O := by
    intro c hc
    have : E ⊔ O ≤ (E ⊔ O).comap (MulAut.conj c).toMonoidHom :=
      sup_le (fun x hx => hEO c hc x hx)
        (fun x hx => Subgroup.mem_sup_right (hOn c hc x hx))
    intro x hx
    simpa using this hx
  set O₁ : Subgroup ↥C := O.subgroupOf C with hO₁
  set E₁ : Subgroup ↥C := E.subgroupOf C with hE₁
  haveI : O₁.Normal := ⟨fun x hx g => by
    rw [hO₁, Subgroup.mem_subgroupOf] at hx ⊢
    exact hOn g g.2 x hx⟩
  haveI : (E₁ ⊔ O₁).Normal := by
    rw [hE₁, hO₁, ← Subgroup.subgroupOf_sup hEC hOC]
    exact ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hN g g.2 x hx⟩
  have hOodd : Odd (Nat.card O₁) := by
    rw [hO₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
    exact hO
  have hE₁2 : IsPGroup 2 E₁ := hE.comap_subtype
  obtain ⟨o', ho', n', hn', hon⟩ := exists_mul_normalizer hOodd hE₁2 (⟨c, hc⟩ : ↥C)
  refine ⟨o', Subgroup.mem_subgroupOf.mp ho', n', n'.2, ?_, congrArg Subtype.val hon⟩
  rw [Subgroup.mem_normalizer_iff] at hn' ⊢
  intro x
  by_cases hx : x ∈ C
  · have := hn' ⟨x, hx⟩
    rw [hE₁, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
    exact this
  · constructor
    · intro hxE
      exact absurd (hEC hxE) hx
    · intro hxE
      apply absurd _ hx
      have h1 := hEC hxE
      have h2 := C.mul_mem (C.mul_mem (C.inv_mem n'.2) h1) n'.2
      simpa [mul_assoc] using h2

end Ambient

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
