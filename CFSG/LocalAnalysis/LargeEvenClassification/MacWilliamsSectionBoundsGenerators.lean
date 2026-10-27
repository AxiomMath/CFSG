module

public import CFSG.LocalAnalysis.LargeEvenClassification.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LargeEvenClassification.Helpers

universe sourceUniverse targetUniverse

theorem elementary_surjection_card_le_pow_generators
    {Source : Type sourceUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [CommGroup Target] [Finite Target]
    {prime : ℕ} (hprime : prime.Prime)
    [Module (ZMod prime) (Additive Target)]
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    (generators : Finset Source)
    (hgenerates : Subgroup.closure (generators : Set Source) = ⊤) :
    Nat.card Target ≤ prime ^ generators.card := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : NeZero prime := ⟨hprime.ne_zero⟩
  have hdimension := quotient_frattini_dimension_le_generators (prime := prime) quotient hsurjective
    generators hgenerates
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod prime) (V := Additive Target)
  have hfieldCard : Nat.card (ZMod prime) = prime := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have htargetCard : Nat.card (Additive Target) = Nat.card Target :=
    Nat.card_congr Additive.ofMul.symm
  rw [htargetCard, hfieldCard] at hcard
  rw [hcard]
  exact Nat.pow_le_pow_right hprime.pos hdimension

theorem elementary_surjection_card_le_pow_generators_of_exponent
    {Source : Type sourceUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] [Finite Target]
    {prime : ℕ} (hprime : prime.Prime) (hcommutative : IsMulCommutative Target)
    (hexponent : ∀ element : Target, element ^ prime = 1)
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    (generators : Finset Source)
    (hgenerates : Subgroup.closure (generators : Set Source) = ⊤) :
    Nat.card Target ≤ prime ^ generators.card := by
  let : CommGroup Target := { (inferInstance : Group Target) with
    mul_comm := @mul_comm' Target _ hcommutative }
  let : Module (ZMod prime) (Additive Target) := elementaryZModModule hexponent
  exact elementary_surjection_card_le_pow_generators hprime quotient hsurjective
    generators hgenerates

theorem elementary_surjection_card_le_pow_generators_of_isElementaryAbelian
    {Source : Type sourceUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] [Finite Target]
    {prime : ℕ} (hprime : prime.Prime) (helementary : CFSG.IsElementaryAbelian prime Target)
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    (generators : Finset Source)
    (hgenerates : Subgroup.closure (generators : Set Source) = ⊤) :
    Nat.card Target ≤ prime ^ generators.card := by
  exact elementary_surjection_card_le_pow_generators_of_exponent hprime
    helementary.toIsMulCommutative
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp helementary.exponent_dvd_p)
    quotient hsurjective generators hgenerates

theorem subgroup_generators_of_ambient_generators
    {Ambient : Type sourceUniverse} [Group Ambient] (U : Subgroup Ambient)
    (generators : Finset Ambient)
    (hgenerates : Subgroup.closure (generators : Set Ambient) = U) :
    ∃ lifted : Finset U, lifted.card = generators.card ∧
      Subgroup.closure (lifted : Set U) = ⊤ := by
  classical
  have hmem : ∀ element ∈ generators, element ∈ U := by
    intro element helement
    rw [← hgenerates]
    exact Subgroup.subset_closure helement
  let lift : generators → U := fun element => ⟨element.val, hmem element.val element.property⟩
  have hlift : Function.Injective lift := by
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun element : U => element.val) heq
  let lifted : Finset U := generators.attach.image lift
  have hcard : lifted.card = generators.card := by
    rw [Finset.card_image_of_injective _ hlift, Finset.card_attach]
  have himage : lifted.image U.subtype = generators := by
    ext element
    constructor
    · intro helement
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp helement
      obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp hsource
      exact original.property
    · intro helement
      refine Finset.mem_image.mpr ⟨lift ⟨element, helement⟩, ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨element, helement⟩, Finset.mem_attach _ _, rfl⟩
  refine ⟨lifted, hcard, ?_⟩
  apply Subgroup.map_injective U.subtype_injective
  rw [MonoidHom.map_closure, ← Finset.coe_image, himage, hgenerates, Subgroup.map_top]
  exact U.range_subtype.symm

end CFSG.LargeEvenClassification.Helpers
