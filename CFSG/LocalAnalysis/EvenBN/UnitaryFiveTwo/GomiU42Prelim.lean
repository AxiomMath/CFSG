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

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem comm_of_commutator_mem_zpowers {B : Type*} [Group B] {e t x : B}
    (he : ∀ y : B, y * e = e * y) (h3 : orderOf e = 3) (ht : t * t = 1)
    (hx : x * t * x⁻¹ * t⁻¹ ∈ zpowers e) : x * t = t * x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hcomm : Commute (e ^ k) t := Commute.zpow_left (show Commute e t from (he t).symm) k
  have hc : e ^ k * t = x * t * x⁻¹ := by
    rw [hk, inv_mul_cancel_right]
  have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [ht]; simp
  rw [← hc] at hsq
  have hee : e ^ k * e ^ k = 1 := by
    have key : (e ^ k * t) * (e ^ k * t) = (e ^ k * e ^ k) * (t * t) := by
      calc (e ^ k * t) * (e ^ k * t) = e ^ k * (t * e ^ k) * t := by simp only [mul_assoc]
        _ = e ^ k * (e ^ k * t) * t := by rw [← hcomm.eq]
        _ = (e ^ k * e ^ k) * (t * t) := by simp only [mul_assoc]
    rw [key, ht, mul_one] at hsq
    exact hsq
  rw [← zpow_add] at hee
  have hd : ((orderOf e : ℕ) : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.mpr hee
  have h3k : (3 : ℤ) ∣ k := by
    rw [h3] at hd
    push_cast at hd
    omega
  have he1 : e ^ k = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [h3]
    exact_mod_cast h3k
  have h1 : x * t * x⁻¹ * t⁻¹ = 1 := hk.symm.trans he1
  have h2 : x * t * x⁻¹ = t := mul_inv_eq_one.mp h1
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [h2]

theorem centralizer_quotient_zpowers {B : Type*} [Group B] {e t : B} [(zpowers e).Normal]
    (he : ∀ y : B, y * e = e * y) (h3 : orderOf e = 3) (ht : t * t = 1) :
    centralizer ({(QuotientGroup.mk t : B ⧸ zpowers e)} : Set (B ⧸ zpowers e)) =
      (centralizer ({t} : Set B)).map (QuotientGroup.mk' (zpowers e)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [mem_centralizer_singleton_iff] at hz
    have hmem : x * t * x⁻¹ * t⁻¹ ∈ zpowers e := by
      apply (QuotientGroup.eq_one_iff _).mp
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hz]
      group
    have hxt : x * t = t * x := comm_of_commutator_mem_zpowers he h3 ht hmem
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact hxt
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    rw [mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hy]

theorem isPerfect_normalClosure_of_perfect {B : Type*} [Group B] {J : Subgroup B}
    (hJ : ⁅J, J⁆ = J) :
    ⁅normalClosure (J : Set B), normalClosure (J : Set B)⁆ = normalClosure (J : Set B) := by
  apply le_antisymm
  · exact commutator_le_left _ _
  · apply normalClosure_le_normal
    have hJle : J ≤ ⁅normalClosure (J : Set B), normalClosure (J : Set B)⁆ :=
      calc J = ⁅J, J⁆ := hJ.symm
        _ ≤ ⁅normalClosure (J : Set B), normalClosure (J : Set B)⁆ :=
          commutator_mono Subgroup.le_normalClosure Subgroup.le_normalClosure
    exact fun x hx => hJle hx

theorem exists_not_comm_of_dvd {F : Type*} [Group F] [Finite F] {a : F} {k : ℕ}
    (hF : 2 ^ k ∣ Nat.card F) (hC : ¬ 2 ^ k ∣ Nat.card (centralizer ({a} : Set F))) :
    ∀ S : Sylow 2 F, a ∈ S → ∃ s ∈ S, s * a ≠ a * s := by
  intro S _
  by_contra hcon
  push Not at hcon
  have hle : (S : Subgroup F) ≤ centralizer ({a} : Set F) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact hcon s hs
  have hne : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have hk : k ≤ Nat.factorization (Nat.card F) 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hF
  have hS : 2 ^ k ∣ Nat.card S := by
    rw [Sylow.card_eq_multiplicity]
    exact pow_dvd_pow 2 hk
  exact hC (dvd_trans hS (Subgroup.card_dvd_of_le hle))

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
