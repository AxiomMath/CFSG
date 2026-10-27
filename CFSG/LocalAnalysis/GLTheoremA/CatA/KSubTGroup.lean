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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KSubT

variable {H : Type} [Group H]

theorem card_le_three_of_cyclic [Finite H] (S : Subgroup H) [IsCyclic S]
    (hexp : ∀ x ∈ S, x ^ 3 = 1) : Nat.card S ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp (g : H) g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hg] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem isPGroup_three_of_pow (S : Subgroup H) (hexp : ∀ x ∈ S, x ^ 3 = 1) :
    IsPGroup 3 S :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hexp (g : H) g.2)⟩

theorem exists_mem_not_mem_centralizer [Finite H] {D J : Subgroup H} (hD : Nat.card D = 3 ^ 2)
    (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hsyl : ∀ S : Subgroup H, S ≤ Subgroup.centralizer (J : Set H) → IsPGroup 3 S → IsCyclic S) :
    ∃ d ∈ D, d ∉ Subgroup.centralizer (J : Set H) := by
  by_contra hcon
  have hall : ∀ d ∈ D, d ∈ Subgroup.centralizer (J : Set H) := by
    intro d hd
    by_contra hdn
    exact hcon ⟨d, hd, hdn⟩
  have hle : D ≤ Subgroup.centralizer (J : Set H) := fun d hd => hall d hd
  haveI hcyc : IsCyclic D := hsyl D hle (isPGroup_three_of_pow D hDexp)
  have h3 := card_le_three_of_cyclic D hDexp
  rw [hD] at h3
  norm_num at h3

theorem inf_centralizer_singleton_eq [Finite H] {D J : Subgroup H} {a d : H}
    (hD : Nat.card D = 3 ^ 2) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (haD : a ∈ D) (ha1 : a ≠ 1) (haJ : ∀ x ∈ J, x * a = a * x)
    (hdD : d ∈ D) (hdJ : d ∉ Subgroup.centralizer (J : Set H)) :
    J ⊓ Subgroup.centralizer ({d} : Set H) = J ⊓ Subgroup.centralizer (D : Set H) := by
  have ha3 : a ^ 3 = 1 := hDexp a haD
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hzaJ : Subgroup.zpowers a ≤ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    exact haJ x hx
  have hd_not_za : d ∉ Subgroup.zpowers a := fun h => hdJ (hzaJ h)
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxJ, hxd⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxd
    refine ⟨hxJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨T, hT⟩ : ∃ T : Subgroup H, T = D ⊓ Subgroup.centralizer ({x} : Set H) := ⟨_, rfl⟩
    have hTD : T ≤ D := by
      rw [hT]
      exact inf_le_left
    have hmemT : ∀ y, y ∈ T ↔ y ∈ D ∧ y * x = x * y := by
      intro y
      rw [hT, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    have hza_T : Subgroup.zpowers a ≤ T := by
      rw [Subgroup.zpowers_le, hmemT]
      exact ⟨haD, (haJ x hxJ).symm⟩
    have hdT : d ∈ T := (hmemT d).2 ⟨hdD, hxd.symm⟩
    have hcardT : Nat.card ↥T ∣ 3 ^ 2 := by
      rw [← hD]
      exact Subgroup.card_dvd_of_le hTD
    obtain ⟨k, hk, hkT⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hcardT
    have hza_le : Nat.card ↥(Subgroup.zpowers a) ≤ Nat.card ↥T :=
      Subgroup.card_le_of_le hza_T
    have hTeq : T = D := by
      interval_cases k
      · exfalso
        simp only [pow_zero] at hkT
        omega
      · exfalso
        have hTz : Subgroup.zpowers a = T :=
          Subgroup.eq_of_le_of_card_ge hza_T (le_of_eq (by simp [hza, hkT]))
        apply hd_not_za
        rw [hTz]
        exact hdT
      · exact Subgroup.eq_of_le_of_card_ge hTD (le_of_eq (by rw [hD, hkT]))
    have heT : e ∈ T := by
      rw [hTeq]
      exact he
    exact ((hmemT e).1 heT).2
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxJ, hxD⟩ := hx
    refine ⟨hxJ, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxD
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxD d hdD).symm

end CFSG.LocalAnalysis.GLTheoremA.KSubT
