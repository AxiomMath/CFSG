module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentSubnormal
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.ComponentOddDisplacements

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.SemisimpleLocalContainment

theorem normalizes_components {G : Type*} [Group G] [Finite G]
    (element : G) (horder : orderOf element = 2)
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (hcenter : ∀ component : Subgroup G, IsComponentOf component ⊤ → Subgroup.center component = ⊥)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) :
    localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype ≤
      Subgroup.normalizer (component : Set G) := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  let localLayer := layer.subgroupOf centralizer
  have hsubnormal : IsSubnormal localLayer ⊤ :=
    Components.chain_of_mathlib_subnormal (inferInstance : localLayer.Normal).isSubnormal
  rcases TwoComponentSubnormal.contains_or_normalizes_core localComponent localLayer hlocal hsubnormal with
    hcontained | ⟨_, hcommutator⟩
  · have hlayerNormalizes : layer ≤ Subgroup.normalizer (component : Set G) := by
      apply sSup_le
      intro other hother
      by_cases heq : other = component
      · rw [heq]
        exact Subgroup.le_normalizer
      · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne other component hother hcomponent heq)).trans
            (Subgroup.centralizer_le_normalizer _)
    intro member hmember
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    exact hlayerNormalizes (hcontained hlift)
  · let oddSubgroup := ((componentClassificationOddCore localComponent).map localComponent.subtype).map
      centralizer.subtype
    let core := componentClassificationOddCore localComponent
    let coreMap : core →* oddSubgroup :=
      (centralizer.subtype.comp localComponent.subtype).domRestrict core |>.codRestrict oddSubgroup
        (fun member => Subgroup.mem_map_of_mem centralizer.subtype
          (Subgroup.mem_map_of_mem localComponent.subtype member.property))
    have hsurjective : Function.Surjective coreMap := by
      intro member
      obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp member.property
      obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hlift
      exact ⟨⟨original, horiginal⟩, Subtype.ext heq⟩
    have hodd : Odd (Nat.card oddSubgroup) := (OddCore.odd_card localComponent).of_dvd_nat
      (CFSG.card_dvd_of_surjective coreMap hsurjective)
    let automorphism : MulAut G := MulAut.conj element
    let action : localComponent →* MulAut G :=
      MulAut.conj.comp (centralizer.subtype.comp localComponent.subtype)
    have hinvolutive : Function.Involutive automorphism := by
      intro member
      have hsquare : automorphism * automorphism = 1 := by
        change MulAut.conj element * MulAut.conj element = 1
        have helementSquare : element * element = 1 := by
          have hpower := pow_orderOf_eq_one element
          rwa [horder, pow_two] at hpower
        rw [← map_mul, helementSquare, map_one]
      exact congrArg (fun value : MulAut G => value member) hsquare
    have hcommutes : ∀ actor : localComponent, Commute automorphism (action actor) := by
      intro actor
      have heq := Subgroup.mem_centralizer_singleton_iff.mp actor.val.property
      exact (show Commute element actor.val.val from heq.symm).map MulAut.conj
    have hdisplacement : ∀ actor : localComponent, ∀ member ∈ layer,
        automorphism member = member → member⁻¹ * (action actor) member ∈ oddSubgroup := by
      intro actor member hmember hfixed
      have hcentralizer : member ∈ centralizer := by
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          change element * member * element⁻¹ = member at hfixed
          calc
            member * element = (element * member * element⁻¹) * element := by rw [hfixed]
            _ = element * member := by group
      have hlocalMem : (⟨member, hcentralizer⟩ : centralizer) ∈ localLayer := hmember
      have hcommMem : ⁅(⟨member, hcentralizer⟩ : centralizer)⁻¹, actor.val⁆ ∈
            ⁅localComponent, localLayer⁆ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator (localLayer.inv_mem hlocalMem) actor.property
      have himage := Subgroup.mem_map_of_mem centralizer.subtype (hcommutator hcommMem)
      simp only [commutatorElement_def, inv_inv] at himage
      change member⁻¹ * actor.val.val * member * (actor.val.val)⁻¹ ∈ oddSubgroup at himage
      change member⁻¹ * (actor.val.val * member * (actor.val.val)⁻¹) ∈ oddSubgroup
      simpa only [mul_assoc] using himage
    let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
    intro actor hactor
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hactor
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact ComponentOddDisplacements.component_image_eq_self action automorphism hinvolutive hcommutes
      oddSubgroup hodd hdisplacement component hcomponent (heven component hcomponent)
      (hcenter component hcomponent) (⟨lift, hlift⟩ : localComponent)

theorem component_enters_layer {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (horder : orderOf element = 2)
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)))
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent) :
    localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ Layer.subgroup G := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let image := localComponent.map centralizer.subtype
  let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
  let : Group.IsPerfect image := Group.IsPerfect.map centralizer.subtype
  have hfitting : Fitting.subgroup G = ⊥ :=
    hfree (Fitting.subgroup G) (Fitting.normal G) (Fitting.solvable G)
  apply GeneralizedFitting.perfect_normalizer_enters_layer image
  · rw [hfitting, Subgroup.commutator_bot_right]
  · exact normalizes_components element horder localComponent hlocal heven
      (RadicalFreeLayer.component_center_eq_bot hfree)
  · exact houter

end CFSG.ComponentClassification.SemisimpleLocalContainment
