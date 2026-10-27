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

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped commutatorElement

theorem not_dvd_card_center_of_perfect {G : Type*} [Group G] [Finite G]
    (hG : commutator G = ⊤) {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ^ 2 ∣ Nat.card (G ⧸ Subgroup.center G)) :
    ¬ p ∣ Nat.card (Subgroup.center G) := by
  intro hpZ
  have hpp : p.Prime := Fact.out
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  let f0 : P.toSubgroup →* G ⧸ Subgroup.center G :=
    (QuotientGroup.mk' (Subgroup.center G)).comp P.toSubgroup.subtype
  have hRdvd : Nat.card f0.range ∣ p ^ n := by
    rw [← hn, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f0).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨m, hm_le, hm_eq⟩ := (Nat.dvd_prime_pow hpp).1 hRdvd
  have hRZ : Nat.card f0.range ∣ Nat.card (G ⧸ Subgroup.center G) :=
    Subgroup.card_subgroup_dvd_card _
  have hm1 : m ≤ 1 := by
    by_contra hcon
    have h2 : p ^ 2 ∣ Nat.card f0.range := by
      rw [hm_eq]
      exact pow_dvd_pow p (by omega)
    exact hp (dvd_trans h2 hRZ)
  have hcyc : IsCyclic f0.range := by
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rw [pow_zero] at hm_eq
      have hsub : Subsingleton f0.range := (Nat.card_eq_one_iff_unique.mp hm_eq).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hm_eq
      exact isCyclic_of_prime_card hm_eq
  have hker : f0.rangeRestrict.ker ≤ Subgroup.center P.toSubgroup := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 := congrArg Subtype.val hx
    have h2 : ((x : G) : G ⧸ Subgroup.center G) = 1 := h1
    have hxZ : (x : G) ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).mp h2
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (g : G)
  have hPmc : IsMulCommutative P.toSubgroup :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f0.rangeRestrict hker
  have hPab : ∀ a b : P.toSubgroup, a * b = b * a := fun a b => hPmc.is_comm.comm a b
  let _ : CommGroup P.toSubgroup :=
    { (inferInstance : Group P.toSubgroup) with mul_comm := hPab }
  have hVG : ∀ g : G, MonoidHom.transfer (MonoidHom.id P.toSubgroup) g = 1 := by
    have hle : commutator G ≤ (MonoidHom.transfer (MonoidHom.id P.toSubgroup)).ker := by
      unfold commutator
      apply Subgroup.commutator_le.mpr
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    intro g
    have hg : g ∈ commutator G := by
      rw [hG]
      exact Subgroup.mem_top g
    exact (MonoidHom.mem_ker).mp (hle hg)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpZ
  have hzZ : (z : G) ∈ Subgroup.center G := z.2
  have hord : orderOf (z : G) = p := (Subgroup.orderOf_coe z).trans hz
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * (z : G) ^ k * g₀ ∈ P.toSubgroup →
      g₀⁻¹ * (z : G) ^ k * g₀ = (z : G) ^ k := by
    intro k g₀ _
    have hk : (z : G) ^ k ∈ Subgroup.center G := pow_mem hzZ k
    rw [Subgroup.mem_center_iff.mp hk g₀⁻¹]
    simp
  have hV := hVG (z : G)
  rw [MonoidHom.transfer_eq_pow (MonoidHom.id P.toSubgroup) (z : G) key] at hV
  have h2 : (z : G) ^ P.toSubgroup.index = 1 := congrArg Subtype.val hV
  have hdvd : orderOf (z : G) ∣ P.toSubgroup.index := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at hdvd
  exact Sylow.not_dvd_index P hdvd

end CFSG.AGLEmbeddingD2.McLaughlin

end
