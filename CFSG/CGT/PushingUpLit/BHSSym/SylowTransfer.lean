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

namespace CFSG.CGT.PushingUpLit.BHSSym

open scoped Pointwise

theorem exists_conj_le_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {T : Subgroup G} (hT : IsPGroup p T) (hTidx : ¬ p ∣ T.index) {H : Subgroup G} (hTH : T ≤ H)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQH : Q ≤ H) :
    ∃ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ T := by
  have hT' : IsPGroup p (T.subgroupOf H) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hQ' : IsPGroup p (Q.subgroupOf H) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hidx : ¬ p ∣ (T.subgroupOf H).index := fun h =>
    hTidx (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))
  let ST : Sylow p H := hT'.toSylow hidx
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H S ST
  refine ⟨h, h.2, fun x hx => ?_⟩
  have h1 : (⟨x, hQH hx⟩ : H) ∈ (S : Subgroup H) :=
    hS (by simpa [Subgroup.mem_subgroupOf] using hx)
  have h2 : (MulAut.conj h) • (⟨x, hQH hx⟩ : H) ∈ MulAut.conj h • (S : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [← Sylow.coe_subgroup_smul, hh] at h2
  have h3 : h * ⟨x, hQH hx⟩ * h⁻¹ ∈ (ST : Subgroup H) := by simpa using h2
  have h4 : (ST : Subgroup H) = T.subgroupOf H := rfl
  rw [h4, Subgroup.mem_subgroupOf] at h3
  simpa using h3

@[expose] def setStab {α : Type*} (A : Set α) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, g x ∈ A ↔ x ∈ A}
  mul_mem' {a b} ha hb := fun x => by
    show a (b x) ∈ A ↔ x ∈ A
    rw [ha, hb]
  one_mem' := fun x => Iff.rfl
  inv_mem' {a} ha := fun x => by
    have := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x by simp] at this
    exact this.symm

theorem le_setStab {α : Type*} {A : Set α} {T : Subgroup (Equiv.Perm α)}
    (h : ∀ t ∈ T, ∀ x, t x ∈ A ↔ x ∈ A) : T ≤ setStab A := fun t ht => h t ht

theorem swap_mem_setStab {α : Type*} [DecidableEq α] {A : Set α} {a b : α} (ha : a ∈ A)
    (hb : b ∈ A) : Equiv.swap a b ∈ setStab A := fun x => by
  by_cases hxa : x = a
  · rw [hxa, Equiv.swap_apply_left]
    exact ⟨fun _ => ha, fun _ => hb⟩
  · by_cases hxb : x = b
    · rw [hxb, Equiv.swap_apply_right]
      exact ⟨fun _ => hb, fun _ => ha⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

end CFSG.CGT.PushingUpLit.BHSSym
