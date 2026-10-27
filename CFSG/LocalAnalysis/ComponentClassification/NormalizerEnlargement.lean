module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentTransport
public import CFSG.LocalAnalysis.ComponentClassification.BadComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentCentralizers

public section

open CFSG.Open

namespace CFSG.ComponentClassification.NormalizerEnlargement

theorem enlargement_le_normalizer {G : Type*} [Group G]
    (subgroup centralSubgroup : Subgroup G) (hcentral : centralSubgroup ≤ Subgroup.center G) :
    subgroup ⊔ centralSubgroup ≤ Subgroup.normalizer (subgroup : Set G) :=
  sup_le Subgroup.le_normalizer (hcentral.trans (Subgroup.center_le_normalizer _))

theorem centralizer_le_normalizer {G : Type*} [Group G]
    (subgroup centralSubgroup : Subgroup G) :
    Subgroup.centralizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G) ≤
      Subgroup.normalizer (subgroup : Set G) := by
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  intro element hmem
  exact Subgroup.mem_centralizer_iff.mpr fun member hmember =>
    Subgroup.mem_centralizer_iff.mp hmem member
      ((le_sup_left : subgroup ≤ subgroup ⊔ centralSubgroup) hmember)

theorem twoComponent_iff {G : Type*} [Group G] [Finite G]
    (subgroup centralSubgroup component : Subgroup G)
    (hsubgroupTwo : IsPGroup 2 subgroup) (hcentralTwo : IsPGroup 2 centralSubgroup)
    (hcentral : centralSubgroup ≤ Subgroup.center G) :
    (component ≤ Subgroup.normalizer (subgroup : Set G) ∧
      TwoComponents.IsTwoComponent
        (component.subgroupOf (Subgroup.normalizer (subgroup : Set G)))) ↔
    (component ≤ Subgroup.normalizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G) ∧
      TwoComponents.IsTwoComponent
        (component.subgroupOf
          (Subgroup.normalizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G)))) := by
  let smaller := Subgroup.normalizer (subgroup : Set G)
  let larger := Subgroup.normalizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G)
  let centralizer := Subgroup.centralizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G)
  let : centralSubgroup.Normal := ⟨by
    intro member hmember actor
    rw [Subgroup.mem_center_iff.mp (hcentral hmember) actor]
    simpa only [mul_inv_cancel_right] using hmember⟩
  have hsmallerLarger : smaller ≤ larger :=
    Subgroup.normalizer_le_normalizer_sup_normal (H := subgroup) (K := centralSubgroup)
  have henlargementSmaller : subgroup ⊔ centralSubgroup ≤ smaller :=
    enlargement_le_normalizer subgroup centralSubgroup hcentral
  have henlargementLarger : subgroup ⊔ centralSubgroup ≤ larger := Subgroup.le_normalizer
  have henlargementTwo : IsPGroup 2 (subgroup ⊔ centralSubgroup : Subgroup G) :=
    hsubgroupTwo.to_sup_of_normal_right hcentralTwo
  have hcentralizerSmaller : centralizer ≤ smaller :=
    centralizer_le_normalizer subgroup centralSubgroup
  have hcentralizerLarger : centralizer ≤ larger := Subgroup.centralizer_le_normalizer _
  have hcentralizerChain : (centralizer.subgroupOf larger).IsSubnormal :=
    Subgroup.IsSubnormal.step _ ⊤ le_top Subgroup.IsSubnormal.top inferInstance
  constructor
  · rintro ⟨hle, hcomponent⟩
    have hleCentralizer : component ≤ centralizer :=
      TwoComponentCentralizers.le_ambient_centralizer component
        (subgroup ⊔ centralSubgroup) smaller hle henlargementSmaller hsmallerLarger
        hcomponent henlargementTwo
    have hlocal := TwoComponentTransport.restrict_nested component centralizer smaller
      hleCentralizer hcentralizerSmaller hcomponent
    exact ⟨hle.trans hsmallerLarger, TwoComponentTransport.extend_nested component
      centralizer larger hleCentralizer hcentralizerLarger hcentralizerChain hlocal⟩
  · rintro ⟨hle, hcomponent⟩
    have hleCentralizer : component ≤ centralizer :=
      TwoComponentCentralizers.le_ambient_centralizer component
        (subgroup ⊔ centralSubgroup) larger hle henlargementLarger le_rfl
        hcomponent henlargementTwo
    have hleSmaller := hleCentralizer.trans hcentralizerSmaller
    exact ⟨hleSmaller, TwoComponentTransport.restrict_nested component smaller larger
      hleSmaller hsmallerLarger hcomponent⟩

theorem badSubgroup_eq {G : Type*} [Group G] [Finite G]
    (subgroup centralSubgroup : Subgroup G)
    (hsubgroupTwo : IsPGroup 2 subgroup) (hcentralTwo : IsPGroup 2 centralSubgroup)
    (hcentral : centralSubgroup ≤ Subgroup.center G) :
    (TwoComponents.badSubgroup (Subgroup.normalizer (subgroup : Set G))).map
        (Subgroup.normalizer (subgroup : Set G)).subtype =
      (TwoComponents.badSubgroup
        (Subgroup.normalizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G))).map
          (Subgroup.normalizer ((subgroup ⊔ centralSubgroup : Subgroup G) : Set G)).subtype := by
  rw [BadComponents.ambient_description, BadComponents.ambient_description]
  congr 1
  ext component
  constructor
  · rintro ⟨hle, hcomponent, hnotQuasisimple⟩
    obtain ⟨hleLarger, hcomponentLarger⟩ :=
      (twoComponent_iff subgroup centralSubgroup component hsubgroupTwo hcentralTwo hcentral).mp
        ⟨hle, hcomponent⟩
    exact ⟨hleLarger, hcomponentLarger, hnotQuasisimple⟩
  · rintro ⟨hle, hcomponent, hnotQuasisimple⟩
    obtain ⟨hleSmaller, hcomponentSmaller⟩ :=
      (twoComponent_iff subgroup centralSubgroup component hsubgroupTwo hcentralTwo hcentral).mpr
        ⟨hle, hcomponent⟩
    exact ⟨hleSmaller, hcomponentSmaller, hnotQuasisimple⟩

end CFSG.ComponentClassification.NormalizerEnlargement
