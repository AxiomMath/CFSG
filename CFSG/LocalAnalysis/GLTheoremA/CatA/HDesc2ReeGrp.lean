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

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

section Embed

theorem exists_injective_hom_of_not_dvd_index {r : ℕ} [Fact r.Prime] {P : Type*} [Group P] [Finite P]
    (R : Subgroup P) (hR : ¬ r ∣ R.index) {E : Subgroup P} (hE : IsPGroup r E) :
    ∃ φ : E →* R, Function.Injective φ := by
  classical
  obtain ⟨S⟩ : Nonempty (Sylow r R) := inferInstance
  have hS'p : IsPGroup r ((S : Subgroup R).map R.subtype) := S.isPGroup'.map R.subtype
  have hS'idx : ¬ r ∣ ((S : Subgroup R).map R.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h1 | h1
    · exact S.not_dvd_index h1
    · exact hR h1
  let S₁ : Sylow r P := hS'p.toSylow hS'idx
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  let ψ : ↥Q ≃* ↥S₁ := Sylow.equiv Q S₁
  let Φ : ↥E →* R :=
    (Subgroup.subtype (S : Subgroup R)).comp
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.toMonoidHom.comp
        (ψ.toMonoidHom.comp (Subgroup.inclusion hQ)))
  refine ⟨Φ, ?_⟩
  have e1 : Function.Injective (Subgroup.inclusion hQ) := Subgroup.inclusion_injective hQ
  have e2 : Function.Injective ψ.toMonoidHom := ψ.injective
  have e3 : Function.Injective
      (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.toMonoidHom :=
    MulEquiv.injective _
  have e4 : Function.Injective (Subgroup.subtype (S : Subgroup R)) := Subtype.val_injective
  exact e4.comp (e3.comp (e2.comp e1))

theorem exists_injective_hom_of_le {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {P R E : Subgroup G} (hRP : R ≤ P) (hidx : ¬ r ∣ R.relIndex P) (hEP : E ≤ P)
    (hE : IsPGroup r E) : ∃ φ : E →* R, Function.Injective φ := by
  classical
  have hE' : IsPGroup r (E.subgroupOf P) := by
    intro x
    obtain ⟨k, hk⟩ := hE ⟨x.1.1, x.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  obtain ⟨φ, hφ⟩ := exists_injective_hom_of_not_dvd_index (r := r) (R.subgroupOf P) hidx hE'
  let e₁ : E ≃* E.subgroupOf P := (Subgroup.subgroupOfEquivOfLe hEP).symm
  let e₂ : R.subgroupOf P ≃* R := Subgroup.subgroupOfEquivOfLe hRP
  refine ⟨e₂.toMonoidHom.comp (φ.comp e₁.toMonoidHom), ?_⟩
  exact e₂.injective.comp (hφ.comp e₁.injective)

end Embed

section Counting

theorem card_le_of_embeds_in_cyclic {E C : Type*} [Group E] [Group C] [IsCyclic C] (φ : E →* C)
    (hφ : Function.Injective φ) {r : ℕ} (hr : 0 < r) (h : ∀ x : E, x ^ r = 1) :
    Nat.card E ≤ r := by
  classical
  let e : E ≃* φ.range := MonoidHom.ofInjective hφ
  haveI : IsCyclic φ.range := inferInstance
  haveI : IsCyclic E := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : orderOf g ∣ r := orderOf_dvd_of_pow_eq_one (h g)
  rw [← hord]
  exact Nat.le_of_dvd hr hdvd

theorem card_eq_one_of_not_dvd {r : ℕ} [Fact r.Prime] {G : Type*} [Group G] [Finite G]
    {E P : Subgroup G} (hEP : E ≤ P) (hE : IsPGroup r E) (h : ¬ r ∣ Nat.card P) :
    Nat.card E = 1 := by
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card P := Subgroup.card_dvd_of_le hEP
  rw [hk] at hdvd
  rcases k with _ | k
  · simpa using hk
  · exact absurd (dvd_trans (dvd_pow_self r (Nat.succ_ne_zero k)) hdvd) h

end Counting

end CFSG.LocalAnalysis.GLTheoremA.HDesc
