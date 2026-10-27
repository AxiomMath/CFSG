module

public import CFSG.LocalAnalysis.ComponentClassification.SubgroupOddCoreNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public section

namespace CFSG.ComponentClassification.TwoActionDisplacementEmbedding

theorem displacement_mem {G : Type*} [Group G] (ambient acting fixed : Subgroup G)
    (hfixed : fixed ≤ ambient) (hdisjoint : Disjoint ambient acting)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (actor : G) (hactor : actor ∈ ambient)
    (hproductNormalizes : actor ∈ Subgroup.normalizer ((fixed ⊔ acting : Subgroup G) : Set G))
    (member : G) (hmember : member ∈ acting) :
    member⁻¹ * (actor * member * actor⁻¹) ∈ fixed := by
  have hfixedNormalizes : acting ≤ Subgroup.normalizer (fixed : Set G) :=
    hcentralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hproduct : member⁻¹ * (actor * member * actor⁻¹) ∈ fixed ⊔ acting :=
    (fixed ⊔ acting).mul_mem ((fixed ⊔ acting).inv_mem ((le_sup_right : acting ≤ fixed ⊔ acting) hmember))
      ((Subgroup.mem_normalizer_iff.mp hproductNormalizes member).mp
        ((le_sup_right : acting ≤ fixed ⊔ acting) hmember))
  have hambient : member⁻¹ * (actor * member * actor⁻¹) ∈ ambient := by
    have hconjugate := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (ambient : Set G)).inv_mem (hnormalizes hmember)) actor).mp hactor
    have hmem := ambient.mul_mem hconjugate (ambient.inv_mem hactor)
    convert hmem using 1
    group
  exact (NormalizedProduct.inf_eq fixed acting ambient hfixedNormalizes hfixed hdisjoint) ▸
    (show member⁻¹ * (actor * member * actor⁻¹) ∈ (fixed ⊔ acting) ⊓ ambient from ⟨hproduct, hambient⟩)

theorem embedding {G : Type*} [Group G] (ambient acting intersection fixed : Subgroup G)
    (hfixed : fixed ≤ ambient) (hdisjoint : Disjoint ambient acting)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hcentralizes : acting ≤ Subgroup.centralizer (fixed : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (actor : G) (hactor : actor ∈ ambient) (houtside : actor ∉ intersection)
    (hproductNormalizes : actor ∈ Subgroup.normalizer ((fixed ⊔ acting : Subgroup G) : Set G)) :
    ∃ homomorphism : acting →* Subgroup.center fixed, Function.Injective homomorphism := by
  have hmem := displacement_mem ambient acting fixed hfixed hdisjoint hnormalizes hcentralizes
    actor hactor hproductNormalizes
  have hfixedNormalizes : actor ∈ Subgroup.normalizer (fixed : Set G) := by
    have hambientNormalizes : actor ∈ Subgroup.normalizer (ambient : Set G) := Subgroup.le_normalizer hactor
    have hinf := SubgroupOddCoreNormalizer.inf ambient (fixed ⊔ acting) (Subgroup.zpowers actor)
      (Subgroup.zpowers_le.mpr hambientNormalizes) (Subgroup.zpowers_le.mpr hproductNormalizes)
    have hfixedActing : acting ≤ Subgroup.normalizer (fixed : Set G) :=
      hcentralizes.trans (Subgroup.centralizer_le_normalizer _)
    rw [inf_comm, NormalizedProduct.inf_eq fixed acting ambient hfixedActing hfixed hdisjoint] at hinf
    exact hinf (Subgroup.mem_zpowers actor)
  have hcentral : ∀ member ∈ acting,
      member⁻¹ * (actor * member * actor⁻¹) ∈ Subgroup.centralizer (fixed : Set G) := by
    intro member hmember
    have hconjugateCentral : actor * member * actor⁻¹ ∈ Subgroup.centralizer (fixed : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      have hinverse := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (fixed : Set G)).inv_mem hfixedNormalizes) other).mp hother
      have hcommute := Subgroup.mem_centralizer_iff.mp (hcentralizes hmember) _ hinverse
      have heq := congrArg (fun value : G => actor * value * actor⁻¹) hcommute
      convert heq using 1 <;> group
    exact (Subgroup.centralizer (fixed : Set G)).mul_mem
      ((Subgroup.centralizer (fixed : Set G)).inv_mem (hcentralizes hmember)) hconjugateCentral
  let displacement : acting → Subgroup.center fixed := fun member =>
    ⟨⟨member.val⁻¹ * (actor * member.val * actor⁻¹), hmem member.val member.property⟩,
      Subgroup.mem_center_iff.mpr (fun other => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hcentral member.val member.property) other.val other.property))⟩
  have hidentity : ∀ member : acting,
      actor * member.val * actor⁻¹ = member.val * (displacement member).val.val := by
    intro member
    change actor * member.val * actor⁻¹ = member.val * (member.val⁻¹ * (actor * member.val * actor⁻¹))
    group
  let homomorphism : acting →* Subgroup.center fixed :=
    { toFun := displacement
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change (1 : G)⁻¹ * (actor * 1 * actor⁻¹) = 1
        group
      map_mul' := by
        intro left right
        apply Subtype.ext
        apply Subtype.ext
        change (left.val * right.val)⁻¹ * (actor * (left.val * right.val) * actor⁻¹) =
          (displacement left).val.val * (displacement right).val.val
        have hleft := hidentity left
        have hright := hidentity right
        have hcommute := (Subgroup.mem_centralizer_iff.mp (hcentralizes right.property)
          (displacement left).val.val (displacement left).val.property).symm
        calc
          _ = right.val⁻¹ * left.val⁻¹ * ((actor * left.val * actor⁻¹) *
                (actor * right.val * actor⁻¹)) := by group
          _ = right.val⁻¹ * left.val⁻¹ * ((left.val * (displacement left).val.val) *
                (right.val * (displacement right).val.val)) := by rw [hleft, hright]
          _ = (displacement left).val.val * (displacement right).val.val := by
            calc
              _ = right.val⁻¹ * ((displacement left).val.val * right.val) *
                    (displacement right).val.val := by group
              _ = right.val⁻¹ * (right.val * (displacement left).val.val) *
                    (displacement right).val.val := by rw [hcommute]
              _ = _ := by group }
  refine ⟨homomorphism, (MonoidHom.ker_eq_bot_iff homomorphism).mp ?_⟩
  apply le_antisymm _ bot_le
  intro member hmember
  apply Subgroup.mem_bot.mpr
  by_contra hne
  have hambientNe : member.val ≠ 1 := by
    intro hone
    exact hne (Subtype.ext hone)
  have hdisplacementOne : member.val⁻¹ * (actor * member.val * actor⁻¹) = 1 :=
    congrArg (fun value : Subgroup.center fixed => value.val.val) (MonoidHom.mem_ker.mp hmember)
  have hcommutes : member.val * actor = actor * member.val := by
    have hconjugate := inv_mul_eq_one.mp hdisplacementOne
    exact (mul_inv_eq_iff_eq_mul.mp hconjugate.symm).symm
  exact houtside (hcentralizers member.val member.property hambientNe
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcommutes.symm, hactor⟩)

theorem abelian_of_embedding {Acting Fixed : Type*} [Group Acting] [Group Fixed]
    (homomorphism : Acting →* Subgroup.center Fixed) (hinjective : Function.Injective homomorphism) :
    IsMulCommutative Acting := by
  apply isMulCommutative_iff.mpr
  intro first second
  apply hinjective
  rw [map_mul, map_mul]
  exact mul_comm' _ _

end CFSG.ComponentClassification.TwoActionDisplacementEmbedding
