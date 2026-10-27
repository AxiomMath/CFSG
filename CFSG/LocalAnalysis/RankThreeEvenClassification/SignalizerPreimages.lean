module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeProductFixed
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImages

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem preimage_solvable_prime_complement {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (hkernelSolvable : Group.IsSolvable homomorphism.ker)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (subgroup : Subgroup H) (hsolvable : Group.IsSolvable subgroup)
    (hcomplement : ¬prime ∣ Nat.card subgroup) :
    Group.IsSolvable (subgroup.comap homomorphism) ∧ ¬prime ∣ Nat.card (subgroup.comap homomorphism) := by
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
  have hrestrictedSolvable : Group.IsSolvable restriction.ker := by
    have : Group.IsSolvable homomorphism.ker := hkernelSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := embedding) hembedding
  have hrestrictedComplement : ¬prime ∣ Nat.card restriction.ker :=
    fun hdiv => hkernelComplement (hdiv.trans (Subgroup.card_dvd_of_injective embedding hembedding))
  exact ⟨solvable_of_solvable_kernel_and_range restriction hrestrictionSurjective hrestrictedSolvable hsolvable,
    prime_complement_of_prime_complement_kernel_target prime hprime restriction hrestrictionSurjective
      hrestrictedComplement hcomplement⟩

theorem SignalizerCompatible.comap {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism)
    (actor : Subgroup G) (signalizer : G → Subgroup G) (hpgroup : IsPGroup prime actor)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hkernelCompatible : SignalizerCompatible prime actor signalizer homomorphism.ker)
    (subgroup : Subgroup H)
    (hcompatible : SignalizerCompatible prime (actor.map homomorphism)
      (mappedSignalizer homomorphism actor signalizer) subgroup)
    (hinjective : Set.InjOn homomorphism (actor : Set G)) :
    SignalizerCompatible prime actor signalizer (subgroup.comap homomorphism) := by
  have hpreimage := preimage_solvable_prime_complement prime hprime homomorphism hsurjective
    hkernelCompatible.solvable hkernelCompatible.primeComplement subgroup
      hcompatible.solvable hcompatible.primeComplement
  refine ⟨?_, hpreimage.1, hpreimage.2, ?_⟩
  · apply Subgroup.le_normalizer_iff.mpr
    intro member hmember element helement
    change homomorphism (member * element * member⁻¹) ∈ subgroup
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.le_normalizer_iff.mp hcompatible.normalized (homomorphism member)
      (Subgroup.mem_map_of_mem homomorphism hmember) (homomorphism element) helement
  · intro member hmember hmemberNe element helement
    have hmappedNe : homomorphism member ≠ 1 := by
      intro heq
      exact hmemberNe (hinjective hmember actor.one_mem (heq.trans (map_one homomorphism).symm))
    have himageFixed : homomorphism element ∈ subgroup ⊓
        Subgroup.centralizer ({homomorphism member} : Set H) := by
      refine ⟨helement.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul]
      exact congrArg homomorphism (Subgroup.mem_centralizer_singleton_iff.mp helement.2)
    have himageValue := hcompatible.fixed_le (homomorphism member)
      (Subgroup.mem_map_of_mem homomorphism hmember) hmappedNe himageFixed
    rw [mappedSignalizer_apply_eq homomorphism actor signalizer hinjective member hmember] at himageValue
    obtain ⟨representative, hrepresentative, hrepresentativeEq⟩ := himageValue
    have hdifference : element * representative⁻¹ ∈ homomorphism.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hrepresentativeEq, mul_inv_cancel]
    have hproductMem : element ∈ homomorphism.ker ⊔ signalizer member := by
      have hproduct := Subgroup.mul_mem_sup hdifference hrepresentative
      simpa only [inv_mul_cancel_right] using hproduct
    have hnormalizes : signalizer member ≤ Subgroup.normalizer (homomorphism.ker : Set G) :=
      Subgroup.le_normalizer_of_normal
    have hproductFixed := normalized_sup_centralizer_eq_of_pGroup_prime_complement prime hprime
      (Subgroup.zpowers member) homomorphism.ker (signalizer member)
        (hpgroup.to_le (Subgroup.zpowers_le_of_mem hmember))
        ((Subgroup.zpowers_le_of_mem hmember).trans hkernelCompatible.normalized)
        ((Subgroup.zpowers_le_of_mem hmember).trans
          (signalizer_value_compatible prime hprime actor signalizer hsignalizer member hmember hmemberNe).normalized)
        hnormalizes (fun hdiv => hkernelCompatible.primeComplement
          (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hproductFixed
    have hfixedLe : (homomorphism.ker ⊔ signalizer member) ⊓
        Subgroup.centralizer ({member} : Set G) ≤ signalizer member := by
      rw [hproductFixed]
      exact sup_le (hkernelCompatible.fixed_le member hmember hmemberNe) inf_le_left
    exact hfixedLe ⟨hproductMem, helement.2⟩

end CFSG.RankThreeEvenClassification.Helpers
