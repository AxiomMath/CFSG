module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AbelianActionNorm

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

@[expose, instance_reducible]
def invariantSubgroupAction {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    [MulDistribMulAction actor acted] (subgroup : Subgroup acted)
    (hinvariant : ∀ member : actor, ∀ element ∈ subgroup, member • element ∈ subgroup) :
    MulDistribMulAction actor subgroup where
  smul member element := ⟨member • element, hinvariant member element element.property⟩
  one_smul element := Subtype.ext (one_smul actor (element : acted))
  mul_smul first second element := Subtype.ext (mul_smul first second (element : acted))
  smul_one member := Subtype.ext (smul_one member)
  smul_mul member first second := Subtype.ext (smul_mul' member (first : acted) (second : acted))

@[expose] def invariantQuotientActionHom {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    [MulDistribMulAction actor acted] (subgroup : Subgroup acted) [subgroup.Normal]
    (hinvariant : ∀ member : actor, ∀ element ∈ subgroup, member • element ∈ subgroup)
    (member : actor) : acted ⧸ subgroup →* acted ⧸ subgroup :=
  QuotientGroup.map subgroup subgroup (MulDistribMulAction.toMonoidHom acted member)
    (fun element helement => hinvariant member element helement)

@[expose, instance_reducible]
def invariantQuotientAction {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    [MulDistribMulAction actor acted] (subgroup : Subgroup acted) [subgroup.Normal]
    (hinvariant : ∀ member : actor, ∀ element ∈ subgroup, member • element ∈ subgroup) :
    MulDistribMulAction actor (acted ⧸ subgroup) where
  smul member element := (invariantQuotientActionHom subgroup hinvariant member) element
  one_smul element := by
    induction element using QuotientGroup.induction_on with
    | H representative =>
      change (↑((1 : actor) • representative) : acted ⧸ subgroup) = ↑representative
      rw [one_smul]
  mul_smul first second element := by
    induction element using QuotientGroup.induction_on with
    | H representative =>
      change (↑((first * second) • representative) : acted ⧸ subgroup) =
        ↑(first • (second • representative))
      rw [mul_smul]
  smul_one member := map_one (invariantQuotientActionHom subgroup hinvariant member)
  smul_mul member first second := map_mul (invariantQuotientActionHom subgroup hinvariant member)
    first second

theorem exists_fixed_preimage_of_equivariant_pGroup_prime_complement_kernel
    {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target] [Finite acted]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (homomorphism : acted →* target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker)
    (element : target) (hfixed : ∀ member : actor, member • element = element) :
    ∃ preimage : acted, (∀ member : actor, member • preimage = preimage) ∧
      homomorphism preimage = element := by
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨representative, hrepresentative⟩ := hsurjective element
  let fiber := {preimage : acted // homomorphism preimage = element}
  let action : MulAction actor fiber :=
    { smul := fun member preimage => ⟨member • preimage, by
        rw [hequivariant, preimage.property, hfixed]⟩
      one_smul := fun preimage => Subtype.ext (one_smul actor (preimage : acted))
      mul_smul := fun first second preimage => Subtype.ext (mul_smul first second (preimage : acted)) }
  let : MulAction actor fiber := action
  have hcard : Nat.card fiber = Nat.card homomorphism.ker := by
    simpa only [hrepresentative] using (Nat.card_congr (kernelEquivFiber homomorphism representative)).symm
  obtain ⟨preimage, hpreimage⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card fiber
    (hcard.symm ▸ hkernelComplement)
  refine ⟨preimage, ?_, preimage.property⟩
  intro member
  exact congrArg (fun value : fiber => (value : acted)) (MulAction.mem_fixedPoints.mp hpreimage member)

theorem actionFixedSubgroup_map_le {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (homomorphism : acted →* target)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element) (member : actor) :
    (actionFixedSubgroup member).map homomorphism ≤ actionFixedSubgroup member := by
  rintro element ⟨preimage, hpreimage, rfl⟩
  change member • homomorphism preimage = homomorphism preimage
  rw [← hequivariant]
  exact congrArg homomorphism hpreimage

theorem actionFixedGenerated_map_le {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (homomorphism : acted →* target)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element) :
    (actionFixedGenerated (actor := actor) (acted := acted)).map homomorphism ≤
      actionFixedGenerated (actor := actor) (acted := target) := by
  simp only [actionFixedGenerated, Subgroup.map_iSup]
  apply iSup_le
  intro member
  apply iSup_le
  intro hne
  exact (actionFixedSubgroup_map_le homomorphism hequivariant member).trans
    (le_iSup_of_le member (le_iSup_of_le hne le_rfl))

theorem actionFixedSubgroup_map_eq_of_pGroup_prime_complement_kernel
    {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target] [Finite acted]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (homomorphism : acted →* target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) (member : actor) :
    (actionFixedSubgroup member).map homomorphism = actionFixedSubgroup member := by
  apply le_antisymm (actionFixedSubgroup_map_le homomorphism hequivariant member)
  intro element helement
  have hfixed : member • element = element := helement
  have hcyclicFixed : ∀ other : Subgroup.zpowers member, other • element = element := by
    intro other
    exact MulAction.mem_stabilizer_iff.mp
      ((Subgroup.zpowers_le_of_mem (MulAction.mem_stabilizer_iff.mpr hfixed)) other.property)
  obtain ⟨preimage, hpreimageFixed, hpreimage⟩ :=
    exists_fixed_preimage_of_equivariant_pGroup_prime_complement_kernel prime hprime
      (hpgroup.to_subgroup (Subgroup.zpowers member)) homomorphism hsurjective
      (fun other value => hequivariant other value) hkernelComplement element hcyclicFixed
  refine ⟨preimage, ?_, hpreimage⟩
  exact hpreimageFixed ⟨member, Subgroup.mem_zpowers member⟩

theorem actionFixedGenerated_map_eq_of_pGroup_prime_complement_kernel
    {actor : Type u} {acted : Type v} {target : Type w}
    [Group actor] [Group acted] [Group target] [Finite acted]
    [MulDistribMulAction actor acted] [MulDistribMulAction actor target]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (homomorphism : acted →* target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ member : actor, ∀ element : acted,
      homomorphism (member • element) = member • homomorphism element)
    (hkernelComplement : ¬prime ∣ Nat.card homomorphism.ker) :
    (actionFixedGenerated (actor := actor) (acted := acted)).map homomorphism =
      actionFixedGenerated (actor := actor) (acted := target) := by
  simp only [actionFixedGenerated, Subgroup.map_iSup,
    actionFixedSubgroup_map_eq_of_pGroup_prime_complement_kernel prime hprime hpgroup
      homomorphism hsurjective hequivariant hkernelComplement]

end CFSG.RankThreeEvenClassification.Helpers
