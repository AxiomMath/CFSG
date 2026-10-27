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
public import Mathlib.GroupTheory.Frattini
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem quotient_simple_of_coatom {Ambient : Type groupUniverse} [Group Ambient]
    (MaximalSubgroup : Subgroup Ambient) [MaximalSubgroup.Normal]
    (hmaximal : IsCoatom MaximalSubgroup) : IsSimpleGroup (Ambient ⧸ MaximalSubgroup) := by
  let : Nontrivial (Ambient ⧸ MaximalSubgroup) := QuotientGroup.nontrivial_iff.mpr hmaximal.1
  constructor
  intro QuotientSubgroup _
  let preimage := QuotientSubgroup.comap (QuotientGroup.mk' MaximalSubgroup)
  have hle : MaximalSubgroup ≤ preimage := by
    intro element helement
    change (element : Ambient ⧸ MaximalSubgroup) ∈ QuotientSubgroup
    rw [(QuotientGroup.eq_one_iff element).mpr helement]
    exact QuotientSubgroup.one_mem
  by_cases htop : preimage = ⊤
  · right
    apply top_unique
    intro element _
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective MaximalSubgroup element
    have hrepresentative : representative ∈ preimage := htop ▸ Subgroup.mem_top representative
    exact hrepresentative
  · left
    have heq : preimage = MaximalSubgroup := (hmaximal.le_iff_eq htop).mp hle
    apply le_antisymm _ bot_le
    intro element helement
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective MaximalSubgroup element
    have hpreimage : representative ∈ preimage := helement
    apply Subgroup.mem_bot.mpr
    exact (QuotientGroup.eq_one_iff representative).mpr (heq ▸ hpreimage)

theorem pGroup_coatom_normal {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (MaximalSubgroup : Subgroup Ambient) (hmaximal : IsCoatom MaximalSubgroup) :
    MaximalSubgroup.Normal := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent Ambient := hpgroup.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom MaximalSubgroup
    Group.normalizerCondition_of_isNilpotent hmaximal

theorem pGroup_coatom_quotient_card {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (MaximalSubgroup : Subgroup Ambient) [MaximalSubgroup.Normal]
    (hmaximal : IsCoatom MaximalSubgroup) : Nat.card (Ambient ⧸ MaximalSubgroup) = prime := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsSimpleGroup (Ambient ⧸ MaximalSubgroup) := quotient_simple_of_coatom MaximalSubgroup hmaximal
  have hquotientPGroup := hpgroup.to_quotient MaximalSubgroup
  let : Group.IsNilpotent (Ambient ⧸ MaximalSubgroup) := hquotientPGroup.isNilpotent
  let : CommGroup (Ambient ⧸ MaximalSubgroup) := instCommGroupOfIsSimpleGroupOfIsNilpotent
  have hcardPrime := IsSimpleGroup.prime_card (α := Ambient ⧸ MaximalSubgroup)
  obtain ⟨exponent, hcard⟩ := hquotientPGroup.exists_card_eq
  have hpowerDivides : Nat.card (Ambient ⧸ MaximalSubgroup) ∣ prime ^ exponent := by
    rw [← hcard]
  have hdivides : Nat.card (Ambient ⧸ MaximalSubgroup) ∣ prime :=
    hcardPrime.dvd_of_dvd_pow hpowerDivides
  exact (Nat.dvd_prime hprime).mp hdivides |>.resolve_left hcardPrime.ne_one

theorem pGroup_pow_mem_frattini {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (element : Ambient) : element ^ prime ∈ frattini Ambient := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro MaximalSubgroup hmaximal
  let : MaximalSubgroup.Normal := pGroup_coatom_normal hprime hpgroup MaximalSubgroup hmaximal
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' MaximalSubgroup) (element ^ prime) = 1
  rw [map_pow, ← pGroup_coatom_quotient_card hprime hpgroup MaximalSubgroup hmaximal]
  exact pow_card_eq_one'

theorem pGroup_commutator_mem_frattini {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (first second : Ambient) : first * second * first⁻¹ * second⁻¹ ∈ frattini Ambient := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro MaximalSubgroup hmaximal
  let : Fact prime.Prime := ⟨hprime⟩
  let : MaximalSubgroup.Normal := pGroup_coatom_normal hprime hpgroup MaximalSubgroup hmaximal
  let : IsSimpleGroup (Ambient ⧸ MaximalSubgroup) := quotient_simple_of_coatom MaximalSubgroup hmaximal
  let : Group.IsNilpotent (Ambient ⧸ MaximalSubgroup) :=
    (hpgroup.to_quotient MaximalSubgroup).isNilpotent
  let : CommGroup (Ambient ⧸ MaximalSubgroup) := instCommGroupOfIsSimpleGroupOfIsNilpotent
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' MaximalSubgroup) (first * second * first⁻¹ * second⁻¹) = 1
  simp [mul_comm]

theorem pGroup_frattini_quotient_commutative {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    IsMulCommutative (Ambient ⧸ frattini Ambient) := by
  apply IsMulCommutative.of_comm
  intro first second
  induction first using QuotientGroup.induction_on with
  | H firstRepresentative =>
    induction second using QuotientGroup.induction_on with
    | H secondRepresentative =>
      have hcommutator := (QuotientGroup.eq_one_iff _).mpr
        (pGroup_commutator_mem_frattini hprime hpgroup firstRepresentative secondRepresentative)
      change (QuotientGroup.mk' (frattini Ambient))
        (firstRepresentative * secondRepresentative * firstRepresentative⁻¹ * secondRepresentative⁻¹) = 1
        at hcommutator
      simp only [map_mul, map_inv] at hcommutator
      have hfirst := mul_inv_eq_one.mp hcommutator
      have hsecond := mul_inv_eq_iff_eq_mul.mp hfirst
      exact hsecond

theorem pGroup_frattini_quotient_exponent {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (element : Ambient ⧸ frattini Ambient) : element ^ prime = 1 := by
  induction element using QuotientGroup.induction_on with
  | H representative =>
    have hpower := (QuotientGroup.eq_one_iff _).mpr (pGroup_pow_mem_frattini hprime hpgroup representative)
    exact hpower

end CFSG.LargeEvenClassification.Helpers
