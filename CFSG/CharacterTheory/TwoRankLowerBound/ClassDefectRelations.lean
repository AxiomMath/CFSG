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

open scoped Pointwise Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def subgroupSubconjugate {group : Type*} [Group group] (left right : Subgroup group) : Prop :=
  ∃ conjugator : group, left.map (MulAut.conj conjugator).toMonoidHom ≤ right

@[expose] def subgroupsConjugate {group : Type*} [Group group] (left right : Subgroup group) : Prop :=
  ∃ conjugator : group, left.map (MulAut.conj conjugator).toMonoidHom = right

theorem conjugation_subgroup_map_one {group : Type*} [Group group] (subgroup : Subgroup group) :
    subgroup.map (MulAut.conj (1 : group)).toMonoidHom = subgroup := by
  have hequal : (MulAut.conj (1 : group)).toMonoidHom = MonoidHom.id group := by
    ext element
    simp
  rw [hequal, Subgroup.map_id]

theorem conjugation_subgroup_map_mul {group : Type*} [Group group]
    (subgroup : Subgroup group) (first second : group) :
    (subgroup.map (MulAut.conj first).toMonoidHom).map (MulAut.conj second).toMonoidHom =
      subgroup.map (MulAut.conj (second * first)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext element
  simp [MulAut.conj_apply, mul_assoc]

theorem conjugation_subgroup_card {group : Type*} [Group group]
    (subgroup : Subgroup group) (conjugator : group) :
    Nat.card (subgroup.map (MulAut.conj conjugator).toMonoidHom) = Nat.card subgroup :=
  Nat.card_congr (subgroup.equivMapOfInjective (MulAut.conj conjugator).toMonoidHom
    (MulAut.conj conjugator).injective).toEquiv.symm

theorem subgroupSubconjugate_refl {group : Type*} [Group group] (subgroup : Subgroup group) :
    subgroupSubconjugate subgroup subgroup :=
  ⟨1, by rw [conjugation_subgroup_map_one]⟩

theorem subgroupSubconjugate_of_le {group : Type*} [Group group] {left right : Subgroup group}
    (hcontains : left ≤ right) : subgroupSubconjugate left right :=
  ⟨1, by rwa [conjugation_subgroup_map_one]⟩

theorem subgroupSubconjugate_trans {group : Type*} [Group group]
    {left middle right : Subgroup group} (hfirst : subgroupSubconjugate left middle)
    (hsecond : subgroupSubconjugate middle right) : subgroupSubconjugate left right := by
  obtain ⟨first, hfirst⟩ := hfirst
  obtain ⟨second, hsecond⟩ := hsecond
  refine ⟨second * first, ?_⟩
  rw [← conjugation_subgroup_map_mul]
  exact (Subgroup.map_mono hfirst).trans hsecond

theorem subgroupSubconjugate_card_le {group : Type*} [Group group] [Finite group]
    {left right : Subgroup group} (hconjugate : subgroupSubconjugate left right) :
    Nat.card left ≤ Nat.card right := by
  obtain ⟨conjugator, hcontains⟩ := hconjugate
  simpa only [conjugation_subgroup_card] using Subgroup.card_le_of_le hcontains

theorem subgroupsConjugate_of_subconjugate_card_ge {group : Type*} [Group group] [Finite group]
    {left right : Subgroup group} (hconjugate : subgroupSubconjugate left right)
    (hcard : Nat.card right ≤ Nat.card left) : subgroupsConjugate left right := by
  obtain ⟨conjugator, hcontains⟩ := hconjugate
  refine ⟨conjugator, Subgroup.eq_of_le_of_card_ge hcontains ?_⟩
  rwa [conjugation_subgroup_card]

theorem subgroupsConjugate_subconjugate {group : Type*} [Group group]
    {left right : Subgroup group} (hconjugate : subgroupsConjugate left right) :
    subgroupSubconjugate left right := by
  obtain ⟨conjugator, hequal⟩ := hconjugate
  exact ⟨conjugator, hequal.le⟩

theorem subgroupsConjugate_symm {group : Type*} [Group group]
    {left right : Subgroup group} (hconjugate : subgroupsConjugate left right) :
    subgroupsConjugate right left := by
  obtain ⟨conjugator, hequal⟩ := hconjugate
  refine ⟨conjugator⁻¹, ?_⟩
  rw [← hequal, conjugation_subgroup_map_mul, inv_mul_cancel, conjugation_subgroup_map_one]

theorem subgroupSubconjugate_antisymm {group : Type*} [Group group] [Finite group]
    {left right : Subgroup group} (hfirst : subgroupSubconjugate left right)
    (hsecond : subgroupSubconjugate right left) : subgroupsConjugate left right :=
  subgroupsConjugate_of_subconjugate_card_ge hfirst (subgroupSubconjugate_card_le hsecond)

@[expose] def classDefect {group : Type*} [Group group] (prime : ℕ)
    (conjugacyClass : ConjClasses group) (defect : Subgroup group) : Prop :=
  ∃ representative : group, ConjClasses.mk representative = conjugacyClass ∧
    ∃ sylow : Sylow prime (Subgroup.centralizer ({representative} : Set group)),
      defect = (sylow : Subgroup _).map (Subgroup.centralizer ({representative} : Set group)).subtype

theorem classDefect_exists {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (conjugacyClass : ConjClasses group) :
    ∃ defect : Subgroup group, classDefect prime conjugacyClass defect := by
  obtain ⟨representative, hrepresentative⟩ := ConjClasses.exists_rep conjugacyClass
  let sylow : Sylow prime (Subgroup.centralizer ({representative} : Set group)) := Classical.ofNonempty
  exact ⟨(sylow : Subgroup _).map (Subgroup.centralizer ({representative} : Set group)).subtype,
    representative, hrepresentative, sylow, rfl⟩

theorem classDefect_isPGroup {group : Type*} [Group group]
    {prime : ℕ} {conjugacyClass : ConjClasses group} {defect : Subgroup group}
    (hdefect : classDefect prime conjugacyClass defect) : IsPGroup prime defect := by
  obtain ⟨representative, _, sylow, rfl⟩ := hdefect
  exact sylow.isPGroup'.map _

theorem classDefect_card_le {group : Type*} [Group group] [Finite group]
    {prime : ℕ} {conjugacyClass : ConjClasses group} {defect : Subgroup group}
    (_hdefect : classDefect prime conjugacyClass defect) : Nat.card defect ≤ Nat.card group :=
  Subgroup.card_le_card_group defect

theorem sylow_image_le {group : Type*} [Group group] {prime : ℕ}
    (ambient : Subgroup group) (sylow : Sylow prime ambient) :
    (sylow : Subgroup ambient).map ambient.subtype ≤ ambient := by
  rintro element ⟨member, _, rfl⟩
  exact member.property

theorem p_subgroup_subconjugate_sylow_image {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary ambient : Subgroup group)
    (hprimary : IsPGroup prime primary) (hcontains : primary ≤ ambient)
    (sylow : Sylow prime ambient) :
    subgroupSubconjugate primary ((sylow : Subgroup ambient).map ambient.subtype) := by
  obtain ⟨larger, hlarger⟩ := hprimary.comap_subtype.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq ambient larger sylow
  refine ⟨conjugator.val, ?_⟩
  rintro element ⟨member, hmember, rfl⟩
  let localMember : ambient := ⟨member, hcontains hmember⟩
  have hlocalMember : localMember ∈ (larger : Subgroup ambient) := hlarger hmember
  have hconjugated : (MulAut.conj conjugator) localMember ∈ (sylow : Subgroup ambient) := by
    rw [← hconjugator]
    change (MulAut.conj conjugator) localMember ∈ MulAut.conj conjugator • (larger : Subgroup ambient)
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨localMember, hlocalMember, rfl⟩
  exact Subgroup.mem_map.mpr ⟨(MulAut.conj conjugator) localMember, hconjugated, rfl⟩

theorem conjugation_centralizer_singleton_le {group : Type*} [Group group]
    (element conjugator : group) :
    (Subgroup.centralizer ({element} : Set group)).map (MulAut.conj conjugator).toMonoidHom ≤
      Subgroup.centralizer ({conjugator * element * conjugator⁻¹} : Set group) := by
  rintro other ⟨member, hmember, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hcommute : Commute member element := Subgroup.mem_centralizer_singleton_iff.mp hmember
  exact hcommute.map (MulAut.conj conjugator).toMonoidHom

theorem p_subgroup_subconjugate_classDefect {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group)
    (hprimary : IsPGroup prime primary) (element : group)
    (hcontains : primary ≤ Subgroup.centralizer ({element} : Set group))
    {conjugacyClass : ConjClasses group} (hclass : ConjClasses.mk element = conjugacyClass)
    {defect : Subgroup group} (hdefect : classDefect prime conjugacyClass defect) :
    subgroupSubconjugate primary defect := by
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hdefect
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp
    (ConjClasses.mk_eq_mk_iff_isConj.mp (hclass.trans hrepresentative.symm))
  have hlocal : primary.map (MulAut.conj conjugator).toMonoidHom ≤
      Subgroup.centralizer ({representative} : Set group) := by
    rw [← hconjugator]
    exact (Subgroup.map_mono hcontains).trans (conjugation_centralizer_singleton_le element conjugator)
  have hfirst : subgroupSubconjugate primary
      (primary.map (MulAut.conj conjugator).toMonoidHom) := ⟨conjugator, le_rfl⟩
  exact subgroupSubconjugate_trans hfirst
    (p_subgroup_subconjugate_sylow_image prime _ _ (hprimary.map _) hlocal sylow)

theorem classDefect_subconjugate {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] {conjugacyClass : ConjClasses group}
    {left right : Subgroup group} (hleft : classDefect prime conjugacyClass left)
    (hright : classDefect prime conjugacyClass right) : subgroupSubconjugate left right := by
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hleft
  exact p_subgroup_subconjugate_classDefect prime _ (sylow.isPGroup'.map _) representative
    (sylow_image_le _ sylow) hrepresentative hright

theorem classDefect_conjugate {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] {conjugacyClass : ConjClasses group}
    {left right : Subgroup group} (hleft : classDefect prime conjugacyClass left)
    (hright : classDefect prime conjugacyClass right) : subgroupsConjugate left right :=
  subgroupSubconjugate_antisymm (classDefect_subconjugate prime hleft hright)
    (classDefect_subconjugate prime hright hleft)

end CFSG.TwoRankLowerBound.Helpers
