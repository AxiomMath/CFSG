module

public import CFSG.LocalAnalysis.LargeEvenClassification.GeneratorRank
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeFixedPoints
public import CFSG.LocalAnalysis.LargeEvenClassification.LinearHyperplaneFixed

public section

namespace CFSG.LargeEvenClassification.Helpers

universe actingUniverse groupUniverse

@[expose] def actionFixedSubgroup {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type groupUniverse} [Group Ambient] (action : Acting →* MulAut Ambient)
    (Fixers : Subgroup Acting) : Subgroup Ambient where
  carrier := {element | ∀ fixer : Fixers, action fixer.val element = element}
  one_mem' := fun fixer => map_one (action fixer.val)
  mul_mem' := by
    intro first second hfirst hsecond fixer
    rw [map_mul, hfirst, hsecond]
  inv_mem' := by
    intro element helement fixer
    rw [map_inv, helement]

@[expose] noncomputable def hyperplaneFixedSpan {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type groupUniverse} [Group Ambient] (prime : ℕ) (action : Acting →* MulAut Ambient) :
    Subgroup Ambient :=
  ⨆ Fixers : {Fixers : Subgroup Acting // Fixers.index ≤ prime}, actionFixedSubgroup action Fixers.val

theorem fixed_subgroup_le_hyperplane_span {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type groupUniverse} [Group Ambient] {prime : ℕ} (action : Acting →* MulAut Ambient)
    (Fixers : Subgroup Acting) (hindex : Fixers.index ≤ prime) :
    actionFixedSubgroup action Fixers ≤ hyperplaneFixedSpan prime action :=
  le_iSup_of_le ⟨Fixers, hindex⟩ le_rfl

theorem pGroup_hyperplane_fixed_generation {Acting : Type actingUniverse} [CommGroup Acting]
    [Finite Acting] {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime groupPrime : ℕ} (hprime : prime.Prime) (hgroupPrime : groupPrime.Prime)
    (hneq : prime ≠ groupPrime) (hpacting : IsPGroup prime Acting)
    (hexponent : ∀ element : Acting, element ^ prime = 1) (hpgroup : IsPGroup groupPrime Ambient)
    (action : Acting →* MulAut Ambient) : hyperplaneFixedSpan prime action = ⊤ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact groupPrime.Prime := ⟨hgroupPrime⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hgroupPrime hpgroup
  obtain ⟨module, _, _⟩ := pGroup_frattini_linear_action hgroupPrime hpgroup
  let : Module (ZMod groupPrime) (Additive (Ambient ⧸ frattini Ambient)) := module
  let projection := QuotientGroup.mk' (frattini Ambient)
  let quotientAction : Acting →* MulAut (Ambient ⧸ frattini Ambient) :=
    (frattiniAutAction Ambient).comp action
  let linearAction : Acting →* (Additive (Ambient ⧸ frattini Ambient) ≃ₗ[ZMod groupPrime]
      Additive (Ambient ⧸ frattini Ambient)) :=
    (elementaryAutLinear groupPrime).comp quotientAction
  let representation : Representation (ZMod groupPrime) Acting (Additive (Ambient ⧸ frattini Ambient)) :=
    linearActionRepresentation (ScalarField := ZMod groupPrime) (Acting := Acting)
      (Space := Additive (Ambient ⧸ frattini Ambient)) linearAction
  have hnondividesActing : ¬groupPrime ∣ Nat.card Acting := by
    obtain ⟨exponent, hcard⟩ := hpacting.exists_card_eq
    intro hdivides
    rw [hcard] at hdivides
    exact hneq ((Nat.prime_dvd_prime_iff_eq hgroupPrime hprime).mp
      (hgroupPrime.dvd_of_dvd_pow hdivides)).symm
  let : NeZero (Nat.card Acting : ZMod groupPrime) :=
    ⟨fun hzero => hnondividesActing ((ZMod.natCast_eq_zero_iff _ _).mp hzero)⟩
  have hcoprime : ¬prime ∣ Nat.card Ambient := by
    obtain ⟨exponent, hcard⟩ := hpgroup.exists_card_eq
    intro hdivides
    rw [hcard] at hdivides
    exact hneq ((Nat.prime_dvd_prime_iff_eq hprime hgroupPrime).mp
      (hprime.dvd_of_dvd_pow hdivides))
  let Generators := hyperplaneFixedSpan prime action
  let span := Submodule.span (ZMod groupPrime)
    ((fun element => Additive.ofMul (projection element)) '' (Generators : Set Ambient))
  have hfixedMem : ∀ (vector : representation.asModule), vector ∈ linearHyperplaneFixedVectors (ScalarField := ZMod groupPrime)
      (Acting := Acting) (Space := representation.asModule) prime →
      representation.asModuleEquiv vector ∈ span := by
    intro vector hvector
    obtain ⟨Fixers, hindex, hfixed⟩ := hvector
    let restrictedAction := action.comp Fixers.subtype
    let restrictedQuotientAction := quotientAction.comp Fixers.subtype
    have hequivariant : ∀ element : Fixers, ∀ source : Ambient,
        projection (restrictedAction element source) = restrictedQuotientAction element (projection source) :=
      fun _ _ => rfl
    have htargetFixed : ∀ element : Fixers,
        restrictedQuotientAction element (representation.asModuleEquiv vector).toMul =
          (representation.asModuleEquiv vector).toMul := by
      intro element
      have heq := congrArg representation.asModuleEquiv (hfixed element)
      rw [representation.asModuleEquiv_map_smul, representation.asAlgebraHom_of] at heq
      exact congrArg Additive.toMul heq
    obtain ⟨source, hsource, hsourceFixed⟩ := coprime_fixed_point_lift hprime
      (hpacting.to_subgroup Fixers) restrictedAction restrictedQuotientAction projection
      (QuotientGroup.mk'_surjective _) hequivariant hcoprime
      (representation.asModuleEquiv vector).toMul htargetFixed
    apply Submodule.subset_span
    refine ⟨source, ?_, ?_⟩
    · exact fixed_subgroup_le_hyperplane_span action Fixers hindex hsourceFixed
    · exact congrArg Additive.ofMul hsource
  let preimage := span.comap representation.asModuleEquiv.toLinearMap
  have hspanLe : Submodule.span (ZMod groupPrime)
      (linearHyperplaneFixedVectors (ScalarField := ZMod groupPrime) (Acting := Acting)
        (Space := representation.asModule) prime) ≤ preimage :=
    Submodule.span_le.mpr hfixedMem
  rw [semisimple_hyperplane_fixed_span hprime hexponent] at hspanLe
  have hspanTop : span = ⊤ := by
    apply top_unique
    intro vector _
    have hmem := hspanLe (Submodule.mem_top (x := representation.asModuleEquiv.symm vector))
    change representation.asModuleEquiv (representation.asModuleEquiv.symm vector) ∈ span at hmem
    rw [representation.asModuleEquiv.apply_symm_apply] at hmem
    exact hmem
  have hgenerates := frattini_generators_of_span hgroupPrime hpgroup module
    (Generators : Set Ambient) hspanTop
  rw [Subgroup.closure_eq] at hgenerates
  exact hgenerates

end CFSG.LargeEvenClassification.Helpers
