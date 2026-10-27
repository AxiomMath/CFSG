module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedLift
public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvariantQuotientAction
public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

theorem involution_actor_fixed_lift [Finite G] (actor : A) (hsquare : actor * actor = 1)
    (subgroup : Subgroup G) [subgroup.Normal]
    (hinvariant : InvariantSubgroup (A := A) subgroup)
    (hodd : Odd (Nat.card subgroup))
    (quotient : G ⧸ subgroup)
    (hfixed : let _ := invariantQuotientAction subgroup hinvariant
      actor • quotient = quotient) :
    ∃ element : G, QuotientGroup.mk' subgroup element = quotient ∧ actor • element = element := by
  let _ := invariantQuotientAction subgroup hinvariant
  let cyclic := Subgroup.zpowers actor
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyclic : IsPGroup 2 cyclic := by
    intro element
    refine ⟨1, ?_⟩
    apply Subtype.ext
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp element.property
    change element.val ^ (2 ^ 1) = 1
    rw [← hexponent, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm exponent,
      zpow_mul, zpow_natCast, pow_two, hsquare, one_zpow]
  have hquotientFixed : ∀ element : cyclic, element • quotient = quotient := by
    intro element
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp element.property
    change element.val • quotient = quotient
    rw [← hexponent]
    exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy.mpr hfixed) exponent
  have hker : (QuotientGroup.mk' subgroup).ker = subgroup := QuotientGroup.ker_mk' subgroup
  obtain ⟨representative, hrepresentative⟩ := QuotientGroup.mk'_surjective subgroup quotient
  obtain ⟨element, himage, helement⟩ := coprime_pgroup_fixed_lift (A := cyclic) 2 hcyclic
    (QuotientGroup.mk' subgroup)
    (fun other element => (invariant_quotient_mk_smul subgroup hinvariant other.val element).symm)
    (by
      rw [hker]
      intro hdiv
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv))
    quotient ⟨representative, hrepresentative⟩
    hquotientFixed
  exact ⟨element, himage, helement ⟨actor, Subgroup.mem_zpowers actor⟩⟩

theorem involution_actor_quotient_fixedPointFree [Finite G]
    (actor : A) (hsquare : actor * actor = 1)
    (subgroup : Subgroup G) [subgroup.Normal]
    (hinvariant : InvariantSubgroup (A := A) subgroup)
    (hodd : Odd (Nat.card subgroup))
    (hfixedContainment : ∀ element : G, actor • element = element → element ∈ subgroup) :
    let _ := invariantQuotientAction subgroup hinvariant
    MonoidHom.FixedPointFree (fun quotient : G ⧸ subgroup => actor • quotient) := by
  let _ := invariantQuotientAction subgroup hinvariant
  change MonoidHom.FixedPointFree (fun quotient : G ⧸ subgroup => actor • quotient)
  intro quotient hfixed
  obtain ⟨element, himage, helement⟩ :=
    involution_actor_fixed_lift actor hsquare subgroup hinvariant hodd quotient hfixed
  rw [← himage]
  exact (QuotientGroup.eq_one_iff element).mpr (hfixedContainment element helement)

end CFSG.DisconnectedInvolutionGraph.Helpers
