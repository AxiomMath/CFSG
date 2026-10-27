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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

open Pointwise
open scoped commutatorElement

namespace CFSG.ClassicalInvolution.RouteD.Gaps

theorem hom_eq_one_of_perfect_of_solvable {L M : Type*} [Group L] [Group M] [Group.IsSolvable M]
    [hL : Group.IsPerfect L] (f : L →* M) : f = 1 := by
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable M).solvable
  have hd : ∀ k, derivedSeries L k = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [derivedSeries_succ, ih]; exact hL.commutator_eq_top
  have h1 : (derivedSeries L n).map f ≤ derivedSeries M n := map_derivedSeries_le_derivedSeries f n
  rw [hd n, hn] at h1
  ext x
  have hx : f x ∈ (⊥ : Subgroup M) := h1 ⟨x, Subgroup.mem_top x, rfl⟩
  simpa using hx

theorem perm_hom_eq_one_of_perfect {L α : Type*} [Group L] [Group.IsPerfect L] [Finite α]
    (hα : Nat.card α ≤ 4) (f : L →* Equiv.Perm α) : f = 1 := by
  have : Group.IsSolvable (Equiv.Perm α) := Equiv.Perm.isSolvable hα
  exact hom_eq_one_of_perfect_of_solvable f

theorem perfect_smul_eq_of_card_le_four {L α : Type*} [Group L] [Group.IsPerfect L] [MulAction L α]
    [Finite α] (hα : Nat.card α ≤ 4) (l : L) (a : α) : l • a = a := by
  have := perm_hom_eq_one_of_perfect hα (MulAction.toPermHom L α)
  have h := congrArg (fun g => g l a) this
  simpa using h

theorem conjAct_smul_eq_map {H : Type*} [Group H] (g : H) (A : Subgroup H) :
    (ConjAct.toConjAct g) • A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x _ A).mp hx
    exact ⟨y, hy, by simp [ConjAct.smul_def]⟩
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ A).mpr ⟨y, hy, by simp [ConjAct.smul_def]⟩

theorem perfect_le_normalizer_of_card_le_four {H : Type*} [Group H] (P : Subgroup H)
    [Group.IsPerfect P] (S : Set (Subgroup H)) (hS : S.Finite) (hcard : S.ncard ≤ 4)
    (hstable : ∀ g ∈ P, ∀ A ∈ S, A.map (MulAut.conj g).toMonoidHom ∈ S) {A : Subgroup H}
    (hA : A ∈ S) : P ≤ Subgroup.normalizer (A : Set H) := by
  classical
  have : Finite S := hS.to_subtype
  let _ : MulAction P S :=
    { smul := fun g B => ⟨(ConjAct.toConjAct (g : H)) • B.1, by
          rw [conjAct_smul_eq_map]; exact hstable g g.2 B.1 B.2⟩
      one_smul := fun B => Subtype.ext (by
        show (ConjAct.toConjAct ((1 : P) : H)) • B.1 = B.1
        rw [Subgroup.coe_one, map_one, one_smul])
      mul_smul := fun g h B => Subtype.ext (by
        show (ConjAct.toConjAct (((g * h : P)) : H)) • B.1 =
          (ConjAct.toConjAct (g : H)) • ((ConjAct.toConjAct (h : H)) • B.1)
        rw [Subgroup.coe_mul, map_mul, mul_smul]) }
  intro g hg
  have hc : Nat.card S ≤ 4 := by rw [Nat.card_coe_set_eq]; exact hcard
  have h := perfect_smul_eq_of_card_le_four (L := P) (α := S) hc ⟨g, hg⟩ ⟨A, hA⟩
  have h' := congrArg Subtype.val h
  change (ConjAct.toConjAct g) • A = A at h'
  rw [conjAct_smul_eq_map] at h'
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h'

theorem perfect_le_of_forall_commutator_mem {H : Type*} [Group H] (S C : Subgroup H)
    (hS : ⁅S, S⁆ = S) (h : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ C) : S ≤ C := by
  rw [← hS]
  exact Subgroup.commutator_le.mpr h

theorem perfect_le_centralizer_of_commuting_conj {H : Type*} [Group H] (S P : Subgroup H)
    (hS : ⁅S, S⁆ = S) (hN : S ≤ Subgroup.normalizer (P : Set H))
    (h : ∀ s ∈ S, ∀ s' ∈ S, ∀ p ∈ P,
      s * (s' * p * s'⁻¹) * s⁻¹ = s' * (s * p * s⁻¹) * s'⁻¹) :
    S ≤ Subgroup.centralizer (P : Set H) := by
  refine perfect_le_of_forall_commutator_mem S _ hS fun s hs s' hs' => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hmem : ∀ g ∈ S, ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hN hg) x).mp hx
  have hmem' : ∀ g ∈ S, ∀ x ∈ P, g⁻¹ * x * g ∈ P := fun g hg x hx => by
    have := hmem g⁻¹ (S.inv_mem hg) x hx
    simpa using this
  have hx : s⁻¹ * s'⁻¹ * p * s' * s ∈ P := by
    have h1 := hmem' s' hs' p hp
    have h2 := hmem' s hs _ h1
    simpa [mul_assoc] using h2
  have key := h s hs s' hs' _ hx
  have e1 : s * (s' * (s⁻¹ * s'⁻¹ * p * s' * s) * s'⁻¹) * s⁻¹ =
      ⁅s, s'⁆ * p * ⁅s, s'⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  have e2 : s' * (s * (s⁻¹ * s'⁻¹ * p * s' * s) * s⁻¹) * s'⁻¹ = p := by group
  rw [e1, e2] at key
  rw [mul_inv_eq_iff_eq_mul] at key
  exact key.symm

end CFSG.ClassicalInvolution.RouteD.Gaps
