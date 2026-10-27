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

namespace CFSG.LargeEvenClassification.Helpers

universe actingUniverse sourceUniverse targetUniverse

theorem coprime_action_invariant_sylow {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type sourceUniverse} [Group Ambient] [Finite Ambient] {prime sylowPrime : ℕ}
    (hprime : prime.Prime) (hsylowPrime : sylowPrime.Prime) (hpgroup : IsPGroup prime Acting)
    (action : Acting →* MulAut Ambient) (hcoprime : ¬prime ∣ Nat.card Ambient) :
    ∃ SylowSubgroup : Sylow sylowPrime Ambient, ∀ element : Acting,
      (SylowSubgroup : Subgroup Ambient).map (action element).toMonoidHom = SylowSubgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  let : MulDistribMulAction Acting Ambient := MulDistribMulAction.compHom Ambient action
  have hsylowCard : Nat.card (Sylow sylowPrime Ambient) ∣ Nat.card Ambient := by
    let SylowSubgroup : Sylow sylowPrime Ambient := Classical.choice inferInstance
    exact (SylowSubgroup.card_dvd_index).trans (Subgroup.index_dvd_card _)
  have hcard : ¬prime ∣ Nat.card (Sylow sylowPrime Ambient) := by
    exact fun hdivides => hcoprime (hdivides.trans hsylowCard)
  obtain ⟨SylowSubgroup, hfixed⟩ :=
    hpgroup.nonempty_fixed_point_of_prime_not_dvd_card (Sylow sylowPrime Ambient) hcard
  refine ⟨SylowSubgroup, ?_⟩
  intro element
  have hsubgroup := congrArg (fun entry : Sylow sylowPrime Ambient => (entry : Subgroup Ambient))
    (hfixed element)
  rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hsubgroup
  exact hsubgroup

theorem coprime_fixed_point_lift {Acting : Type actingUniverse} [Group Acting]
    {Source : Type sourceUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ} (hprime : prime.Prime)
    (hpgroup : IsPGroup prime Acting) (action : Acting →* MulAut Source)
    (targetAction : Acting →* MulAut Target) (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient)
    (hequivariant : ∀ element : Acting, ∀ source : Source,
      quotient (action element source) = targetAction element (quotient source))
    (hcoprime : ¬prime ∣ Nat.card Source) (target : Target)
    (hfixed : ∀ element : Acting, targetAction element target = target) :
    ∃ source : Source, quotient source = target ∧ ∀ element : Acting, action element source = source := by
  let : Fact prime.Prime := ⟨hprime⟩
  let Fiber := {source : Source // quotient source = target}
  let : MulAction Acting Fiber := {
    smul := fun element source => ⟨action element source, by
      rw [hequivariant, source.property, hfixed]⟩
    one_smul := by
      intro source
      apply Subtype.ext
      change action 1 source = source
      rw [map_one]
      rfl
    mul_smul := by
      intro first second source
      apply Subtype.ext
      change action (first * second) source = action first (action second source)
      rw [map_mul]
      rfl }
  obtain ⟨lift, hlift⟩ := hsurjective target
  let fiberEquivalence : quotient.ker ≃ Fiber := {
    toFun := fun element => ⟨element.val * lift, by rw [map_mul, element.property, hlift, one_mul]⟩
    invFun := fun element => ⟨element.val * lift⁻¹, by
      change quotient (element.val * lift⁻¹) = 1
      rw [map_mul, map_inv, element.property, hlift, mul_inv_cancel]⟩
    left_inv := by intro element; apply Subtype.ext; group
    right_inv := by intro element; apply Subtype.ext; group }
  have hcard : ¬prime ∣ Nat.card Fiber := by
    rw [← Nat.card_congr fiberEquivalence]
    exact fun hdivides => hcoprime (hdivides.trans quotient.ker.card_subgroup_dvd_card)
  obtain ⟨source, hsource⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card Fiber hcard
  refine ⟨source, source.property, ?_⟩
  intro element
  exact congrArg Subtype.val (hsource element)

end CFSG.LargeEvenClassification.Helpers
