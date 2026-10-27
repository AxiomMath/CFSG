module

public import CFSG.LocalAnalysis.ComponentClassification.RadicalFreeLayer
public import CFSG.LocalAnalysis.ComponentClassification.PrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CentralComponentQuotients

public section

open CFSG.Open

namespace CFSG.ComponentClassification.GeneralizedFitting

@[expose] noncomputable def subgroup (G : Type*) [Group G] : Subgroup G :=
  CFSG.WholeGroup.fstarOf (Layer.subgroup G)

theorem subgroup.eq_sup (G : Type*) [Group G] :
    subgroup G = Fitting.subgroup G ⊔ Layer.subgroup G :=
  rfl

attribute [eqns subgroup.eq_sup] subgroup

theorem characteristic (G : Type*) [Group G] : (subgroup G).Characteristic := by
  let : (Fitting.subgroup G).Characteristic := Fitting.characteristic G
  let : (Layer.subgroup G).Characteristic := Layer.characteristic G
  rw [subgroup]
  infer_instance

theorem normal (G : Type*) [Group G] : (subgroup G).Normal := by
  let : (subgroup G).Characteristic := characteristic G
  infer_instance

theorem normal_monotone {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] :
    (subgroup normalSubgroup).map normalSubgroup.subtype ≤ subgroup G := by
  rw [subgroup, Subgroup.map_sup]
  apply sup_le
  · exact (PrimeCore.fitting_normal_monotone normalSubgroup).trans le_sup_left
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hcomponent
    exact Subgroup.map_le_iff_le_comap.mp ((Layer.component_le
      (LocalComponents.of_subnormal_subgroup normalSubgroup
        (Components.chain_of_mathlib_subnormal
          (inferInstance : normalSubgroup.Normal).isSubnormal) component hcomponent)).trans le_sup_right)

theorem commutative_of_le_center (G : Type*) [Group G] [Finite G]
    (hcentral : subgroup G ≤ Subgroup.center G) : IsMulCommutative G := by
  have hlayerCentral : Layer.subgroup G ≤ Subgroup.center G := le_sup_right.trans hcentral
  let : Group.IsPerfect (Layer.subgroup G) := Layer.perfect G
  have hlayerBot : Layer.subgroup G = ⊥ := Quasisimple.perfect_le_center_eq_bot _ hlayerCentral
  let radical := SolvableRadical.subgroup G
  let : radical.Normal := SolvableRadical.normal G
  let : Group.IsSolvable radical := SolvableRadical.solvable G
  have hradicalCentral : radical ≤ Subgroup.center G :=
    Fitting.radical_le_center_of_fitting_le_center (le_sup_left.trans hcentral)
  have hradicalTop : radical = ⊤ := by
    by_contra hne
    let : Nontrivial (G ⧸ radical) := QuotientGroup.nontrivial_iff.mpr hne
    obtain ⟨component, hcomponent⟩ := RadicalFreeLayer.exists_component
      (SolvableRadical.quotient_free G)
    have hkernel : (QuotientGroup.mk' radical).ker ≤ Subgroup.center G := by
      rw [QuotientGroup.ker_mk']
      exact hradicalCentral
    have hmap := CentralComponentQuotients.layer_map (QuotientGroup.mk' radical)
      (QuotientGroup.mk'_surjective _) hkernel
    rw [hlayerBot, Subgroup.map_bot] at hmap
    have hcomponentBot : component = ⊥ := le_bot_iff.mp (hmap ▸ Layer.component_le hcomponent)
    exact (component.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hcomponent.2.2)) hcomponentBot
  apply Subgroup.center_eq_top_iff.mp
  apply top_unique
  rwa [hradicalTop] at hradicalCentral

theorem centralizer_le_fitting (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (subgroup G : Set G) ≤ Fitting.subgroup G := by
  let generalized := subgroup G
  let : generalized.Normal := normal G
  let centralizer := Subgroup.centralizer (generalized : Set G)
  have hintrinsic : subgroup centralizer ≤ Subgroup.center centralizer := by
    intro member hmember
    have hambient : member.val ∈ generalized := normal_monotone centralizer
      (Subgroup.mem_map_of_mem centralizer.subtype hmember)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp other.property member.val hambient).symm
  let : IsMulCommutative centralizer := commutative_of_le_center centralizer hintrinsic
  let : Group.IsNilpotent centralizer := Fitting.nilpotent_of_commutator_le_center
    (by rw [(commutator_eq_bot_iff centralizer).mpr inferInstance]; exact bot_le)
  exact Fitting.maximal centralizer

theorem centralizer_le (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (subgroup G : Set G) ≤ subgroup G :=
  (centralizer_le_fitting G).trans le_sup_left

theorem fitting_layer_commute (G : Type*) [Group G] [Finite G] :
    ⁅Fitting.subgroup G, Layer.subgroup G⁆ = ⊥ := by
  let : (Fitting.subgroup G).Normal := Fitting.normal G
  let : Group.IsSolvable (Fitting.subgroup G) := Fitting.solvable G
  rw [Subgroup.commutator_comm]
  exact Layer.commutes_with_solvable_subnormal _
    (Components.chain_of_mathlib_subnormal (inferInstance : (Fitting.subgroup G).Normal).isSubnormal)

theorem perfect_normalizer_enters_layer {G : Type*} [Group G] [Finite G]
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hcentralizesFitting : ⁅perfectSubgroup, Fitting.subgroup G⁆ = ⊥)
    (hnormalizes : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      perfectSubgroup ≤ Subgroup.normalizer (component : Set G))
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    perfectSubgroup ≤ Layer.subgroup G := by
  let fitting := Fitting.subgroup G
  let layer := Layer.subgroup G
  let : fitting.Normal := Fitting.normal G
  let : layer.Normal := Layer.normal G
  let : Group.IsSolvable fitting := Fitting.solvable G
  have hcontained : perfectSubgroup ≤ fitting ⊔ layer := by
    intro actor hactor
    have hinner : ∀ component : Subgroup G, IsComponentOf component ⊤ →
        ∃ implementer ∈ component, ∀ member ∈ component,
          actor * member * actor⁻¹ = implementer * member * implementer⁻¹ := by
      intro component hcomponent
      let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
      let : Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)) :=
        houter component hcomponent
      let : Group.IsSolvable (OuterAutomorphisms.Outer component) :=
        OuterAutomorphisms.solvable_of_centerQuotient component
      exact ComponentInnerActions.perfect_normalizer_action_inner perfectSubgroup component
        (hnormalizes component hcomponent) (⟨actor, hactor⟩ : perfectSubgroup)
    obtain ⟨implementer, himplementer, haction⟩ :=
      ComponentInnerActions.exists_layer_implementer actor hinner
    have hcentralizesLayer : implementer⁻¹ * actor ∈ Subgroup.centralizer (layer : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have heq := congrArg (fun value : G => implementer⁻¹ * value * actor)
        (haction member hmember)
      calc
        member * (implementer⁻¹ * actor) = implementer⁻¹ * (implementer * member * implementer⁻¹) * actor := by group
        _ = implementer⁻¹ * (actor * member * actor⁻¹) * actor := heq.symm
        _ = (implementer⁻¹ * actor) * member := by group
    have hcentralizesF : implementer⁻¹ * actor ∈ Subgroup.centralizer (fitting : Set G) := by
      apply Subgroup.mul_mem
      · apply Subgroup.inv_mem
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact fitting_layer_commute G) himplementer
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralizesFitting hactor
    have hcentralizes : implementer⁻¹ * actor ∈ Subgroup.centralizer (subgroup G : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      have hbound : fitting ⊔ layer ≤ Subgroup.centralizer ({implementer⁻¹ * actor} : Set G) := by
        apply sup_le
        · intro member hmember
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          exact Subgroup.mem_centralizer_iff.mp hcentralizesF member hmember
        · intro member hmember
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          exact Subgroup.mem_centralizer_iff.mp hcentralizesLayer member hmember
      intro member hmember
      exact Subgroup.mem_centralizer_singleton_iff.mp (hbound hmember)
    have hdisplacement := centralizer_le G hcentralizes
    have hproduct := (subgroup G).mul_mem
      ((le_sup_right : layer ≤ subgroup G) himplementer) hdisplacement
    change implementer * (implementer⁻¹ * actor) ∈ fitting ⊔ layer at hproduct
    simpa only [mul_inv_cancel_left] using hproduct
  let quotient := QuotientGroup.mk' fitting
  let : Group.IsSolvable quotient.ker := by
    change Group.IsSolvable (QuotientGroup.mk' fitting).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  apply SolvableKernelContainment.perfect_containment quotient perfectSubgroup layer
  have hmap := Subgroup.map_mono (f := quotient) hcontained
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at hmap
  exact hmap

theorem layer_center_le_fitting (G : Type*) [Group G] [Finite G] :
    (Subgroup.center (Layer.subgroup G)).map (Layer.subgroup G).subtype ≤ Fitting.subgroup G := by
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  let center := Subgroup.center layer
  let : Group.IsNilpotent center := Fitting.nilpotent_of_commutator_le_center
    (by rw [(commutator_eq_bot_iff center).mpr inferInstance]; exact bot_le)
  let image := center.map layer.subtype
  let : image.Normal := ConjAct.normal_of_characteristic_of_normal
  let : Group.IsNilpotent image := (Group.isNilpotent_congr
    (center.equivMapOfInjective layer.subtype layer.subtype_injective)).mp inferInstance
  exact Fitting.maximal image

theorem involution_fixed_layer_centralizer_normalizes {G : Type*} [Group G] [Finite G]
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup] (element : G)
    (hsquare : element * element = 1)
    (hcentralizesElement : perfectSubgroup ≤ Subgroup.centralizer ({element} : Set G))
    (hcentralizesFitting : ⁅perfectSubgroup, Fitting.subgroup G⁆ = ⊥)
    (hcentralizesFixed : ⁅perfectSubgroup,
      Layer.subgroup G ⊓ Subgroup.centralizer ({element} : Set G)⁆ = ⊥)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) :
    perfectSubgroup ≤ Subgroup.normalizer (component : Set G) := by
  apply ComponentAutomorphisms.ambient_normalizes_components perfectSubgroup element hsquare
    hcentralizesElement _ hcentralizesFixed component hcomponent
  apply le_bot_iff.mp
  have hle := Subgroup.commutator_mono (le_rfl : perfectSubgroup ≤ perfectSubgroup)
    (layer_center_le_fitting G)
  rwa [hcentralizesFitting] at hle

end CFSG.ComponentClassification.GeneralizedFitting
