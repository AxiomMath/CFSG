module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSolvableQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem preimage_prime_complement {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism) (hkernel : ¬prime ∣ Nat.card homomorphism.ker)
    (subgroup : Subgroup H) (hcomplement : ¬prime ∣ Nat.card subgroup) :
    ¬prime ∣ Nat.card (subgroup.comap homomorphism) := by
  let preimage := subgroup.comap homomorphism
  let restriction : preimage →* subgroup :=
    { toFun := fun element => ⟨homomorphism element, element.property⟩
      map_one' := Subtype.ext (map_one homomorphism)
      map_mul' := fun first second => Subtype.ext (map_mul homomorphism (first : G) (second : G)) }
  have hrestrictionSurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨representative, heq⟩ := hsurjective element
    refine ⟨⟨representative, ?_⟩, Subtype.ext heq⟩
    change homomorphism representative ∈ subgroup
    exact heq.symm ▸ element.property
  let embedding : restriction.ker →* homomorphism.ker :=
    { toFun := fun element => ⟨((element : preimage) : G),
        congrArg Subtype.val (MonoidHom.mem_ker.mp element.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hembedding : Function.Injective embedding := by
    intro first second heq
    have hvalue : ((first : preimage) : G) = ((second : preimage) : G) :=
      congrArg (fun value : homomorphism.ker => (value : G)) heq
    exact Subtype.ext (Subtype.ext hvalue)
  exact prime_complement_of_prime_complement_kernel_target prime hprime restriction hrestrictionSurjective
    (fun hdiv => hkernel (hdiv.trans (Subgroup.card_dvd_of_injective embedding hembedding))) hcomplement

theorem primeComplementCore_quotient_eq_bot {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) :
    letI := (primeComplementCore_properties G prime hprime).1
    primeComplementCore (G ⧸ primeComplementCore G prime) prime = ⊥ := by
  have : (primeComplementCore G prime).Normal := (primeComplementCore_properties G prime hprime).1
  let quotient := QuotientGroup.mk' (primeComplementCore G prime)
  let quotientCore := primeComplementCore (G ⧸ primeComplementCore G prime) prime
  have hproperties := primeComplementCore_properties (G ⧸ primeComplementCore G prime) prime hprime
  have : quotientCore.Normal := hproperties.1
  have hpreimage : quotientCore.comap quotient ≤ primeComplementCore G prime :=
    le_primeComplementCore prime _ inferInstance
      (preimage_prime_complement prime hprime quotient
        (QuotientGroup.mk'_surjective (primeComplementCore G prime))
        (by rw [QuotientGroup.ker_mk']; exact (primeComplementCore_properties G prime hprime).2)
        quotientCore hproperties.2)
  have hmapped := Subgroup.map_mono (f := quotient) hpreimage
  rw [Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (primeComplementCore G prime))] at hmapped
  have hmapCore : (primeComplementCore G prime).map quotient = ⊥ := by
    apply bot_unique
    rintro element ⟨preimage, hpreimage, rfl⟩
    apply Subgroup.mem_bot.mpr
    apply MonoidHom.mem_ker.mp
    change preimage ∈ (QuotientGroup.mk' (primeComplementCore G prime)).ker
    rw [QuotientGroup.ker_mk']
    exact hpreimage
  exact bot_unique (hmapCore ▸ hmapped)

theorem nilpotent_of_central_kernel {G : Type u} {H : Type v} [Group G] [Group H]
    (homomorphism : G →* H) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G) (hnilpotent : Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  have : Group.IsNilpotent H := hnilpotent
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective homomorphism hsurjective
  have : Group.IsNilpotent (G ⧸ homomorphism.ker) := Group.nilpotent_of_mulEquiv equivalence.symm
  let projection := QuotientGroup.mk' (Subgroup.center G)
  have hkernel : homomorphism.ker ≤ projection.ker := by
    rw [QuotientGroup.ker_mk']
    exact hcentral
  let factor := QuotientGroup.lift homomorphism.ker projection hkernel
  have hfactorSurjective : Function.Surjective factor :=
    QuotientGroup.lift_surjective_of_surjective homomorphism.ker projection
      (QuotientGroup.mk'_surjective (Subgroup.center G)) hkernel
  exact Group.of_quotient_center_nilpotent (Group.nilpotent_of_surjective factor hfactorSurjective)

end CFSG.RankThreeEvenClassification.Helpers
