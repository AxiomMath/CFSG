module

public import CFSG.LocalAnalysis.ComponentClassification.ComponentAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.ComponentInvolutionWitness

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ComponentOddDisplacements

theorem involution_in_odd_subgroup_eq_one {G : Type*} [Group G]
    (oddSubgroup : Subgroup G) (hodd : Odd (Nat.card oddSubgroup)) (member : G)
    (hmember : member ∈ oddSubgroup) (hsquare : member * member = 1) : member = 1 := by
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
    (oddSubgroup.orderOf_dvd_natCard hmember)
    (orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two]))

theorem image_in_involution_pair {G : Type*} [Group G] [Finite G]
    (automorphism transformation : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (hcommutes : Commute automorphism transformation)
    (oddSubgroup : Subgroup G) (hodd : Odd (Nat.card oddSubgroup))
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (hdisplacement : ∀ member ∈ component ⊔ component.map automorphism.toMonoidHom,
      automorphism member = member →
      member⁻¹ * transformation member ∈ oddSubgroup)
    (heven : 2 ∣ Nat.card component) (hcenter : Subgroup.center component = ⊥) :
    component.map transformation.toMonoidHom = component ∨
      component.map transformation.toMonoidHom = component.map automorphism.toMonoidHom := by
  let partner := component.map automorphism.toMonoidHom
  let image := component.map transformation.toMonoidHom
  let partnerImage := partner.map transformation.toMonoidHom
  have hpartner : IsComponentOf partner ⊤ := (LocalComponents.equiv_iff automorphism component).mpr hcomponent
  have himage : IsComponentOf image ⊤ := (LocalComponents.equiv_iff transformation component).mpr hcomponent
  have hpartnerImage : IsComponentOf partnerImage ⊤ :=
    (LocalComponents.equiv_iff transformation partner).mpr hpartner
  have hcomposite : (automorphism.toMonoidHom.comp transformation.toMonoidHom).comp
      automorphism.toMonoidHom = transformation.toMonoidHom := by
    apply MonoidHom.ext
    intro member
    have heq := congrArg (fun value : MulAut G => value (automorphism member)) hcommutes.eq
    change automorphism (transformation (automorphism member)) =
      transformation (automorphism (automorphism member)) at heq
    rwa [hinvolutive] at heq
  have hpartnerDouble : partner.map automorphism.toMonoidHom = component := by
    rw [Subgroup.map_map]
    have hid : automorphism.toMonoidHom.comp automorphism.toMonoidHom = MonoidHom.id G := by
      apply MonoidHom.ext
      exact hinvolutive
    rw [hid, Subgroup.map_id]
  have hpartnerImageDouble : partnerImage.map automorphism.toMonoidHom = image := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomposite]
  by_contra hneither
  have himageNe : image ≠ component := fun heq => hneither (Or.inl heq)
  have himagePartnerNe : image ≠ partner := fun heq => hneither (Or.inr heq)
  have hpartnerImageNe : partnerImage ≠ component := by
    intro heq
    have hmap := congrArg (Subgroup.map automorphism.toMonoidHom) heq
    rw [hpartnerImageDouble] at hmap
    exact himagePartnerNe hmap
  have hpartnerImagePartnerNe : partnerImage ≠ partner := by
    intro heq
    have hmap := congrArg (Subgroup.map automorphism.toMonoidHom) heq
    rw [hpartnerImageDouble, hpartnerDouble] at hmap
    exact himageNe hmap
  let orbit := component ⊔ partner
  have hcentralizes : image ⊔ partnerImage ≤ Subgroup.centralizer (orbit : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    apply sup_le
    · apply Subgroup.le_centralizer_iff.mp
      apply sup_le
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne image component himage hcomponent himageNe)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne partnerImage component hpartnerImage hcomponent hpartnerImageNe)
    · apply Subgroup.le_centralizer_iff.mp
      apply sup_le
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne image partner himage hpartner himagePartnerNe)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne partnerImage partner hpartnerImage hpartner hpartnerImagePartnerNe)
  obtain ⟨member, hmember, hsquare, hfixed, hnotCentralizes⟩ :=
    ComponentInvolutionWitness.exists_fixed_noncentralizing component hcomponent heven hcenter
      automorphism hinvolutive
  have htransformed : transformation member ∈ image ⊔ partnerImage := by
    have hmap := Subgroup.mem_map_of_mem transformation.toMonoidHom hmember
    rw [Subgroup.map_sup] at hmap
    exact hmap
  have hcommute : Commute member (transformation member) :=
    Subgroup.mem_centralizer_iff.mp (hcentralizes htransformed) member hmember
  have htransformedSquare : transformation member * transformation member = 1 := by
    rw [← map_mul, hsquare, map_one]
  have hdisplacementSquare : (member⁻¹ * transformation member) * (member⁻¹ * transformation member) = 1 := by
    rw [← pow_two, hcommute.inv_left.mul_pow, inv_pow, pow_two, pow_two,
      hsquare, htransformedSquare, inv_one, one_mul]
  have hone := involution_in_odd_subgroup_eq_one oddSubgroup hodd _
    (hdisplacement member hmember hfixed) hdisplacementSquare
  have heq : transformation member = member := (inv_mul_eq_one.mp hone).symm
  apply hnotCentralizes
  exact (Subgroup.centralizer_le (le_sup_left : component ≤ orbit))
    (heq ▸ hcentralizes htransformed)

theorem component_image_eq_self {A G : Type*} [Group A] [Group.IsPerfect A]
    [Group G] [Finite G] (action : A →* MulAut G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ∀ actor : A, Commute automorphism (action actor))
    (oddSubgroup : Subgroup G) (hodd : Odd (Nat.card oddSubgroup))
    (hdisplacement : ∀ actor : A, ∀ member ∈ Layer.subgroup G, automorphism member = member →
      member⁻¹ * (action actor) member ∈ oddSubgroup)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (heven : 2 ∣ Nat.card component) (hcenter : Subgroup.center component = ⊥) (actor : A) :
    component.map (action actor).toMonoidHom = component := by
  let permutationAction := ComponentAutomorphisms.subgroupAction action
  let latticeAction : MulAut G →* Equiv.Perm (Subgroup G) :=
    ComponentAutomorphisms.subgroupAction (MonoidHom.id (MulAut G))
  let involution := latticeAction automorphism
  have hinvolution : Function.Involutive involution := by
    intro subgroup
    change (subgroup.map automorphism.toMonoidHom).map automorphism.toMonoidHom = subgroup
    rw [Subgroup.map_map]
    have hid : automorphism.toMonoidHom.comp automorphism.toMonoidHom = MonoidHom.id G := by
      apply MonoidHom.ext
      exact hinvolutive
    rw [hid, Subgroup.map_id]
  have hpermutationCommutes : ∀ acting : A, Commute involution (permutationAction acting) := by
    intro acting
    exact (hcommutes acting).map latticeAction
  have hpair : ∀ acting : A,
      permutationAction acting component = component ∨
        permutationAction acting component = involution component := by
    intro acting
    exact image_in_involution_pair automorphism (action acting) hinvolutive (hcommutes acting)
      oddSubgroup hodd component hcomponent
      (by
        intro member hmember hfixed
        apply hdisplacement acting member _ hfixed
        exact (sup_le (Layer.component_le hcomponent)
          (Layer.component_le ((LocalComponents.equiv_iff automorphism component).mpr hcomponent))) hmember)
      heven hcenter
  exact PerfectPermutationActions.fixed_of_involutive_pair permutationAction involution
    hinvolution hpermutationCommutes component hpair actor

end CFSG.ComponentClassification.ComponentOddDisplacements
