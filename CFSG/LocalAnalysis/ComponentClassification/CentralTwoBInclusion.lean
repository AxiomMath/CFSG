module

public import CFSG.LocalAnalysis.ComponentClassification.LocalB
public import CFSG.LocalAnalysis.ComponentClassification.NormalizerEnlargement

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CentralTwoBInclusion

@[expose] def Property (G : Type*) [Group G] : Prop :=
  ∀ twoSubgroup : Subgroup G, twoSubgroup ≠ ⊥ → IsPGroup 2 twoSubgroup →
    (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
      (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G

theorem normalizer_image {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (subgroup : Subgroup G) (hkernel : quotient.ker ≤ subgroup) :
    (Subgroup.normalizer (subgroup : Set G)).map quotient =
      Subgroup.normalizer (subgroup.map quotient : Set H) := by
  have hpreimage : (Subgroup.normalizer (subgroup.map quotient : Set H)).comap quotient =
      Subgroup.normalizer (subgroup : Set G) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hsurjective,
      Subgroup.comap_map_eq_self hkernel]
  rw [← hpreimage]
  exact Subgroup.map_comap_eq_self_of_surjective hsurjective _

theorem of_central_two_kernel {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker)
    (hquotient : Property H) : Property G := by
  intro twoSubgroup _ htwoSubgroup
  by_cases hcontained : twoSubgroup ≤ quotient.ker
  · let : twoSubgroup.Normal := ⟨by
      intro member hmember actor
      rw [Subgroup.mem_center_iff.mp (hcentralKernel (hcontained hmember)) actor]
      simpa only [mul_inv_cancel_right] using hmember⟩
    have hnormalizer := Subgroup.normalizer_eq_top twoSubgroup
    rw [hnormalizer]
    exact le_of_eq (BadComponents.equiv_invariant (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))
  · let enlargement := twoSubgroup ⊔ quotient.ker
    let normalizer := Subgroup.normalizer (enlargement : Set G)
    let target := twoSubgroup.map quotient
    have htargetNe : target ≠ ⊥ := by
      intro hbot
      exact hcontained ((Subgroup.map_eq_bot_iff twoSubgroup).mp hbot)
    have htargetTwo : IsPGroup 2 target := htwoSubgroup.map quotient
    have henlargementImage : enlargement.map quotient = target := by
      have hpreimage : target.comap quotient = enlargement := Subgroup.comap_map_eq _ _
      rw [← hpreimage]
      exact Subgroup.map_comap_eq_self_of_surjective hsurjective _
    have hnormalizerImage : normalizer.map quotient = Subgroup.normalizer (target : Set H) := by
      rw [normalizer_image quotient hsurjective enlargement le_sup_right, henlargementImage]
    have hbadImage :
        ((TwoComponents.badSubgroup normalizer).map normalizer.subtype).map quotient ≤
          (TwoComponents.badSubgroup G).map quotient := by
      rw [BadComponents.ambient_image_of_central_two_kernel quotient hcentralKernel htwoKernel,
        hnormalizerImage, BadComponents.centralKernel_image quotient hsurjective
          hcentralKernel htwoKernel]
      exact hquotient target htargetNe htargetTwo
    let : Group.IsPerfect (TwoComponents.badSubgroup normalizer) := BadComponents.perfect normalizer
    let : Group.IsPerfect ((TwoComponents.badSubgroup normalizer).map normalizer.subtype) :=
      Group.IsPerfect.map normalizer.subtype
    have hcontainment := BadComponents.perfect_containment_of_central_kernel quotient
      hcentralKernel ((TwoComponents.badSubgroup normalizer).map normalizer.subtype)
        (TwoComponents.badSubgroup G) hbadImage
    rw [NormalizerEnlargement.badSubgroup_eq twoSubgroup quotient.ker htwoSubgroup htwoKernel
      hcentralKernel]
    exact hcontainment

theorem localB_of_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) (hinclusion : Property G) :
    LocalB.LocalBProperty G := LocalB.of_corefree_and_inclusion hcorefree hinclusion

end CFSG.ComponentClassification.CentralTwoBInclusion
