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

namespace CFSG.HardMathSupport.Dickson.I271

section Normal

variable {C : Type*} [Group C] [Finite C]

theorem normal_of_simple_not_dvd_factorial (E : Subgroup C) [IsSimpleGroup ↥E]
    (hn : ¬ Nat.card ↥E ∣ (E.index).factorial) : E.Normal := by
  classical
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Finite (C ⧸ E) := inferInstance
  haveI : Fintype (C ⧸ E) := Fintype.ofFinite _
  have hker : E.normalCore = (MulAction.toPermHom C (C ⧸ E)).ker := Subgroup.normalCore_eq_ker E
  by_cases h : E.normalCore = ⊥
  · exfalso
    have hinj : Function.Injective (MulAction.toPermHom C (C ⧸ E)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← hker]; exact h
    have h1 : Nat.card C ∣ Nat.card (Equiv.Perm (C ⧸ E)) := Subgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (C ⧸ E)), Fintype.card_perm,
      ← Nat.card_eq_fintype_card] at h1
    have h2 : Nat.card ↥E ∣ Nat.card C := Subgroup.card_subgroup_dvd_card E
    exact hn (h2.trans h1)
  · have hK : (E.normalCore.subgroupOf E).Normal := (Subgroup.normalCore_normal E).subgroupOf E
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.normalCore.subgroupOf E) with h0 | h1
    · exfalso
      apply h
      rw [eq_bot_iff]
      intro x hx
      have hxE : x ∈ E := Subgroup.normalCore_le E hx
      have : (⟨x, hxE⟩ : ↥E) ∈ E.normalCore.subgroupOf E := Subgroup.mem_subgroupOf.2 hx
      rw [h0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · rw [Subgroup.subgroupOf_eq_top] at h1
      have : E = E.normalCore := le_antisymm h1 (Subgroup.normalCore_le E)
      rw [this]
      exact Subgroup.normalCore_normal E

end Normal

section Central

theorem normal_sylow_of_central_three {G : Type*} [Group G] [Finite G] (hG : Nat.card G < 18)
    {s : G} (hs : orderOf s = 3) (hsc : ∀ g : G, g * s = s * g) {q : ℕ} [Fact q.Prime]
    (hq3 : q ≠ 3) (hqG : q ∣ Nat.card G) (P : Sylow q G) : (P : Subgroup G).Normal := by
  have hq := (Fact.out : q.Prime)
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G) with hN
  have hsN : s ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have : s * h * s⁻¹ = h := by
      rw [← hsc h]; group
    rw [this]
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have h3N : 3 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hsN
    rwa [hs] at this
  have hPcard : Nat.card P = q ^ (Nat.card G).factorization q := P.card_eq_multiplicity
  have hPN' : Nat.card P ∣ Nat.card N := Subgroup.card_dvd_of_le hPN
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    rw [hPcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3))
  have h3P : 3 * Nat.card P ∣ Nat.card N := hcop.mul_dvd_of_dvd_of_dvd h3N hPN'
  have hqP : q ≤ Nat.card P := by
    rw [hPcard]
    exact Nat.le_self_pow (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqG).ne' q
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have h6 : 6 ≤ Nat.card N := by
    have := Nat.le_of_dvd hNpos h3P
    have := hq.two_le
    omega
  have hidx : N.index * Nat.card N = Nat.card G := Subgroup.index_mul_card N
  have hlt : N.index < 3 := by
    by_contra h
    have h' : 3 ≤ N.index := not_lt.1 h
    nlinarith
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmod : N.index ≡ 1 [MOD q] := by
    have := card_sylow_modEq_one q G
    rwa [Sylow.card_eq_index_normalizer P] at this
  have hone : N.index = 1 := by
    rcases (by omega : N.index = 1 ∨ N.index = 2) with h | h
    · exact h
    · exfalso
      rw [h] at hmod
      have h1 : q ∣ 2 - 1 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
      have : q ∣ 1 := by simpa using h1
      exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have : N = ⊤ := Subgroup.index_eq_one.1 hone
  exact Subgroup.normalizer_eq_top_iff.1 this

variable {C : Type*} [Group C] [Finite C]

theorem isPGroup_three_of_small_central {Z : Subgroup C} [Z.Normal] {s : C}
    (hsZ : s ∈ Z) (hs3 : orderOf s = 3) (hsc : ∀ c : C, c * s = s * c)
    (hcard : Nat.card Z < 18)
    (hO : ∀ N : Subgroup C, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥) : IsPGroup 3 Z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnot
  obtain ⟨q, hq, hqd, hq3⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card Z ∧ q ≠ 3 := by
    by_contra h'
    push Not at h'
    apply hnot
    rw [IsPGroup.iff_card]
    exact ⟨(Nat.card Z).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hp hd => h' d hp hd⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow q Z) := inferInstance
  have hs'3 : orderOf (⟨s, hsZ⟩ : Z) = 3 := by rwa [Subgroup.orderOf_mk]
  have hs'c : ∀ g : Z, g * ⟨s, hsZ⟩ = ⟨s, hsZ⟩ * g := fun g => Subtype.ext (hsc g)
  have hPn : (P : Subgroup Z).Normal :=
    normal_sylow_of_central_three hcard hs'3 hs'c hq3 hqd P
  have hPchar : (P : Subgroup Z).Characteristic := Sylow.characteristic_of_normal P hPn
  have hP'n : ((P : Subgroup Z).map Z.subtype).Normal := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ c
    have hc : (MulAut.conjNormal c : MulAut Z) x ∈ (P : Subgroup Z) := by
      have := hPchar.fixed (MulAut.conjNormal c)
      have hx' : x ∈ (P : Subgroup Z).comap (MulAut.conjNormal c).toMonoidHom := by
        rw [this]; exact hx
      exact hx'
    exact ⟨_, hc, by simp [MulAut.conjNormal_apply]⟩
  have hcard' : Nat.card ((P : Subgroup Z).map Z.subtype) = Nat.card P :=
    Subgroup.card_map_of_injective Z.subtype_injective
  have hPcard : Nat.card P = q ^ (Nat.card Z).factorization q := P.card_eq_multiplicity
  have hcop : Nat.Coprime 3 (Nat.card ((P : Subgroup Z).map Z.subtype)) := by
    rw [hcard', hPcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3))
  have hbot := hO _ hP'n hcop
  have h1 : Nat.card P = 1 := by
    rw [← hcard', hbot]; simp
  have hqP : q ≤ Nat.card P := by
    rw [hPcard]
    exact Nat.le_self_pow (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqd).ne' q
  have := hq.two_le
  omega

end Central

end CFSG.HardMathSupport.Dickson.I271
