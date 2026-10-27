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

namespace CFSG.HardMathSupport.Timmesfeld.Proving

variable {Y : Type*} [Group Y]

abbrev conjActionOfNormalizes (Q K : Subgroup Y) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K) :
    MulAction Q K where
  smul q k := ⟨(q : Y) * k * (q : Y)⁻¹, hQK q q.2 k k.2⟩
  one_smul k := Subtype.ext (by
    change (1 : Y) * (k : Y) * (1 : Y)⁻¹ = k
    group)
  mul_smul a b k := Subtype.ext (by
    change ((a * b : Q) : Y) * (k : Y) * ((a * b : Q) : Y)⁻¹ =
      (a : Y) * ((b : Y) * (k : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

theorem card_fixedPoints_conj_eq (Q K : Subgroup Y) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K) :
    letI := conjActionOfNormalizes Q K hQK
    Nat.card (MulAction.fixedPoints Q K) = Nat.card ↥(K ⊓ Subgroup.centralizer (Q : Set Y)) := by
  letI := conjActionOfNormalizes Q K hQK
  have hF : ∀ k : MulAction.fixedPoints Q K, (k.1 : Y) ∈ K ⊓ Subgroup.centralizer (Q : Set Y) := by
    intro k
    refine Subgroup.mem_inf.mpr ⟨k.1.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hk := MulAction.mem_fixedPoints.mp k.2 ⟨h, hh⟩
    have hk' := congrArg Subtype.val hk
    change (h : Y) * (k.1 : Y) * (h : Y)⁻¹ = (k.1 : Y) at hk'
    rw [mul_inv_eq_iff_eq_mul] at hk'
    exact hk'
  have hG : ∀ g : ↥(K ⊓ Subgroup.centralizer (Q : Set Y)), ∀ q : Q,
      (q : Y) * (g : Y) * (q : Y)⁻¹ = (g : Y) := by
    intro g q
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp g.2).2 (q : Y) q.2
    rw [hc, mul_inv_cancel_right]
  refine Nat.card_congr (Equiv.mk (fun k => ⟨(k.1 : Y), hF k⟩)
    (fun g => ⟨⟨(g : Y), (Subgroup.mem_inf.mp g.2).1⟩, ?_⟩) (fun k => rfl) (fun g => rfl))
  rw [MulAction.mem_fixedPoints]
  intro q
  apply Subtype.ext
  exact hG g q

theorem exists_orderOf_eq_prime_mem_inf_centralizer [Finite Y] {p : ℕ} (hp : p.Prime)
    {Q K : Subgroup Y} (hQ : IsPGroup p Q) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hpK : p ∣ Nat.card K) :
    ∃ x ∈ K ⊓ Subgroup.centralizer (Q : Set Y), orderOf x = p := by
  haveI := Fact.mk hp
  letI := conjActionOfNormalizes Q K hQK
  have hmod : Nat.card K ≡ Nat.card (MulAction.fixedPoints Q K) [MOD p] :=
    hQ.card_modEq_card_fixedPoints K
  rw [card_fixedPoints_conj_eq Q K hQK] at hmod
  have hdvd : p ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (Q : Set Y)) := by
    have h0 : Nat.card K ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpK
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h0)
  haveI : Fintype ↥(K ⊓ Subgroup.centralizer (Q : Set Y)) := Fintype.ofFinite _
  have hdvd' : p ∣ Fintype.card ↥(K ⊓ Subgroup.centralizer (Q : Set Y)) := by
    rw [← Nat.card_eq_fintype_card]
    exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd'
  exact ⟨x.1, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end CFSG.HardMathSupport.Timmesfeld.Proving

end
