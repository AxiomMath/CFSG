module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

open scoped commutatorElement

namespace CFSG.ComponentClassification.FixedCommutingProduct

@[expose] def fixedSubgroup {G : Type*} [Group G] (automorphism : MulAut G) : Subgroup G :=
  automorphism.toMonoidHom.eqLocus (MonoidHom.id G)

theorem inf_le_center {G : Type*} [Group G] (left right : Subgroup G)
    (hcommutes : ⁅left, right⁆ = ⊥) (hcover : left ⊔ right = ⊤) :
    left ⊓ right ≤ Subgroup.center G := by
  have hleftCentralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes
  have hrightCentralizes := Subgroup.le_centralizer_iff.mp hleftCentralizes
  intro element hmem
  have hcentralizer : left ⊔ right ≤ Subgroup.centralizer ({element} : Set G) := by
    apply sup_le
    · intro member hmember
      apply Subgroup.mem_centralizer_iff.mpr
      intro central hcentral
      rw [Set.mem_singleton_iff.mp hcentral]
      exact (Subgroup.mem_centralizer_iff.mp (hrightCentralizes hmem.2) member hmember).symm
    · intro member hmember
      apply Subgroup.mem_centralizer_iff.mpr
      intro central hcentral
      rw [Set.mem_singleton_iff.mp hcentral]
      exact (Subgroup.mem_centralizer_iff.mp (hleftCentralizes hmem.1) member hmember).symm
  rw [hcover] at hcentralizer
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact (Subgroup.mem_centralizer_iff.mp (hcentralizer (Subgroup.mem_top other)) element
    (Set.mem_singleton element)).symm

theorem displacement_mem_inf {G : Type*} [Group G] (left right : Subgroup G)
    (automorphism : MulAut G)
    (hleftInvariant : left.map automorphism.toMonoidHom = left)
    (hrightInvariant : right.map automorphism.toMonoidHom = right)
    (leftMember rightMember : G) (hleftMember : leftMember ∈ left)
    (hrightMember : rightMember ∈ right)
    (hfixed : automorphism (leftMember * rightMember) = leftMember * rightMember) :
    leftMember⁻¹ * automorphism leftMember ∈ left ⊓ right := by
  have hleftImage : automorphism leftMember ∈ left := by
    rw [← hleftInvariant]
    exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hleftMember
  have hrightImage : automorphism rightMember ∈ right := by
    rw [← hrightInvariant]
    exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hrightMember
  have hdisplacement : leftMember⁻¹ * automorphism leftMember =
      rightMember * (automorphism rightMember)⁻¹ := by
    rw [map_mul] at hfixed
    calc
      leftMember⁻¹ * automorphism leftMember =
          leftMember⁻¹ * (automorphism leftMember * automorphism rightMember) *
            (automorphism rightMember)⁻¹ := by group
      _ = rightMember * (automorphism rightMember)⁻¹ := by rw [hfixed]; group
  exact ⟨left.mul_mem (left.inv_mem hleftMember) hleftImage,
    by rw [hdisplacement]; exact right.mul_mem hrightMember (right.inv_mem hrightImage)⟩

theorem fixed_sup_of_disjoint {G : Type*} [Group G] (left right : Subgroup G)
    [left.Normal] (hdisjoint : Disjoint left right) (automorphism : MulAut G)
    (hleftInvariant : left.map automorphism.toMonoidHom = left)
    (hrightInvariant : right.map automorphism.toMonoidHom = right) :
    (left ⊔ right) ⊓ fixedSubgroup automorphism =
      (left ⊓ fixedSubgroup automorphism) ⊔ (right ⊓ fixedSubgroup automorphism) := by
  apply le_antisymm
  · intro member hmember
    obtain ⟨leftMember, hleftMember, rightMember, hrightMember, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hmember.1
    have hdisplacement := displacement_mem_inf left right automorphism hleftInvariant
      hrightInvariant leftMember rightMember hleftMember hrightMember hmember.2
    rw [hdisjoint.eq_bot, Subgroup.mem_bot] at hdisplacement
    have hleftFixed : automorphism leftMember = leftMember :=
      (inv_mul_eq_one.mp hdisplacement).symm
    have hrightFixed : automorphism rightMember = rightMember := by
      have hfixed : automorphism (leftMember * rightMember) = leftMember * rightMember := hmember.2
      rw [map_mul, hleftFixed] at hfixed
      exact mul_left_cancel hfixed
    exact Subgroup.mul_mem_sup ⟨hleftMember, hleftFixed⟩ ⟨hrightMember, hrightFixed⟩
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

theorem commutator_mul_mul {G : Type*} [Group G] (left right : Subgroup G)
    (hcommutes : ⁅left, right⁆ = ⊥) (leftFirst leftSecond : left) (rightFirst rightSecond : right) :
    ⁅leftFirst.val * rightFirst.val, leftSecond.val * rightSecond.val⁆ =
      ⁅leftFirst.val, leftSecond.val⁆ * ⁅rightFirst.val, rightSecond.val⁆ := by
  have hcentralizer := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes
  let product := left.subtype.noncommCoprod right.subtype
    (fun leftMember rightMember =>
      (Subgroup.mem_centralizer_iff.mp (hcentralizer leftMember.property)
        rightMember.val rightMember.property).symm)
  exact (map_commutatorElement product (leftFirst, rightFirst) (leftSecond, rightSecond)).symm

theorem derived_fixed_of_cover {G : Type*} [Group G] (left right : Subgroup G)
    [left.Normal] (hcommutes : ⁅left, right⁆ = ⊥) (hcover : left ⊔ right = ⊤)
    (automorphism : MulAut G)
    (hleftInvariant : left.map automorphism.toMonoidHom = left)
    (hrightInvariant : right.map automorphism.toMonoidHom = right) :
    ⁅fixedSubgroup automorphism, fixedSubgroup automorphism⁆ ≤
      (left ⊓ fixedSubgroup automorphism) ⊔ (right ⊓ fixedSubgroup automorphism) := by
  apply Subgroup.commutator_le.mpr
  intro first hfirst second hsecond
  have hfirstProduct : first ∈ left ⊔ right := by rw [hcover]; exact Subgroup.mem_top _
  have hsecondProduct : second ∈ left ⊔ right := by rw [hcover]; exact Subgroup.mem_top _
  obtain ⟨leftFirst, hleftFirst, rightFirst, hrightFirst, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hfirstProduct
  obtain ⟨leftSecond, hleftSecond, rightSecond, hrightSecond, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hsecondProduct
  have hfixedFirst : automorphism (leftFirst * rightFirst) = leftFirst * rightFirst := hfirst
  have hfixedSecond : automorphism (leftSecond * rightSecond) = leftSecond * rightSecond := hsecond
  have hcentral := inf_le_center left right hcommutes hcover
  have hleftFirstCentral := hcentral (displacement_mem_inf left right automorphism
    hleftInvariant hrightInvariant leftFirst rightFirst hleftFirst hrightFirst hfixedFirst)
  have hleftSecondCentral := hcentral (displacement_mem_inf left right automorphism
    hleftInvariant hrightInvariant leftSecond rightSecond hleftSecond hrightSecond hfixedSecond)
  have hcommutesReverse : ⁅right, left⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
  have hfirstReverse : automorphism (rightFirst * leftFirst) = rightFirst * leftFirst := by
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hleftFirst) rightFirst hrightFirst
    rwa [heq]
  have hsecondReverse : automorphism (rightSecond * leftSecond) = rightSecond * leftSecond := by
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hleftSecond) rightSecond hrightSecond
    rwa [heq]
  have hrightFirstCentral := (inf_le_center right left hcommutesReverse
    ((sup_comm right left).trans hcover)) (displacement_mem_inf right left automorphism
      hrightInvariant hleftInvariant rightFirst leftFirst hrightFirst hleftFirst hfirstReverse)
  have hrightSecondCentral := (inf_le_center right left hcommutesReverse
    ((sup_comm right left).trans hcover)) (displacement_mem_inf right left automorphism
      hrightInvariant hleftInvariant rightSecond leftSecond hrightSecond hleftSecond hsecondReverse)
  have hfixedCommutator : ∀ firstMember secondMember : G,
      firstMember⁻¹ * automorphism firstMember ∈ Subgroup.center G →
      secondMember⁻¹ * automorphism secondMember ∈ Subgroup.center G →
        automorphism ⁅firstMember, secondMember⁆ = ⁅firstMember, secondMember⁆ := by
    intro firstMember secondMember hfirstCentral hsecondCentral
    rw [map_commutatorElement]
    have hfirstFactor : automorphism firstMember =
        firstMember * (firstMember⁻¹ * automorphism firstMember) := by group
    have hsecondFactor : automorphism secondMember =
        secondMember * (secondMember⁻¹ * automorphism secondMember) := by group
    conv_lhs => rw [hfirstFactor, hsecondFactor]
    exact (CentralExtensions.commutator_mul_center_left _ _ _ hfirstCentral).trans
      (CentralExtensions.commutator_mul_center_right _ _ _ hsecondCentral)
  have hleftCommutator : ⁅leftFirst, leftSecond⁆ ∈ left ⊓ fixedSubgroup automorphism :=
    ⟨(Subgroup.commutator_le_self left)
      (Subgroup.commutator_mem_commutator hleftFirst hleftSecond),
      hfixedCommutator leftFirst leftSecond hleftFirstCentral hleftSecondCentral⟩
  have hrightCommutator : ⁅rightFirst, rightSecond⁆ ∈ right ⊓ fixedSubgroup automorphism :=
    ⟨(Subgroup.commutator_le_self right)
      (Subgroup.commutator_mem_commutator hrightFirst hrightSecond),
      hfixedCommutator rightFirst rightSecond hrightFirstCentral hrightSecondCentral⟩
  rw [commutator_mul_mul left right hcommutes (⟨leftFirst, hleftFirst⟩ : left)
    (⟨leftSecond, hleftSecond⟩ : left) (⟨rightFirst, hrightFirst⟩ : right)
      (⟨rightSecond, hrightSecond⟩ : right)]
  exact Subgroup.mul_mem_sup hleftCommutator hrightCommutator

theorem derived_fixed {G : Type*} [Group G] (left right : Subgroup G)
    (hcommutes : ⁅left, right⁆ = ⊥) (automorphism : MulAut G)
    (hleftInvariant : left.map automorphism.toMonoidHom = left)
    (hrightInvariant : right.map automorphism.toMonoidHom = right) :
    ⁅(left ⊔ right) ⊓ fixedSubgroup automorphism,
      (left ⊔ right) ⊓ fixedSubgroup automorphism⁆ ≤
        (left ⊓ fixedSubgroup automorphism) ⊔ (right ⊓ fixedSubgroup automorphism) := by
  let product := left ⊔ right
  have hproductInvariant : product.map automorphism.toMonoidHom = product := by
    rw [Subgroup.map_sup, hleftInvariant, hrightInvariant]
  let productAutomorphism : MulAut product :=
    (automorphism.subgroupMap product).trans (MulEquiv.subgroupCongr hproductInvariant)
  let localLeft := left.subgroupOf product
  let localRight := right.subgroupOf product
  have hleftMap : localLeft.map product.subtype = left := Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hrightMap : localRight.map product.subtype = right := Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hlocalCommutator : ⁅localLeft, localRight⁆ = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ product.subtype_injective).mp
    rw [Subgroup.map_commutator, hleftMap, hrightMap]
    exact hcommutes
  let : localLeft.Normal := by
    apply Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
    rw [inf_eq_left.mpr (le_sup_left : left ≤ product)]
    apply sup_le Subgroup.le_normalizer
    exact (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hlocalCover : localLeft ⊔ localRight = ⊤ := by
    apply Subgroup.map_injective product.subtype_injective
    rw [Subgroup.map_sup, hleftMap, hrightMap]
    ext element
    constructor
    · intro hmem
      exact ⟨⟨element, hmem⟩, Subgroup.mem_top _, rfl⟩
    · rintro ⟨member, _, rfl⟩
      exact member.property
  have hlocalInvariant : ∀ subgroup : Subgroup G,
      subgroup.map automorphism.toMonoidHom = subgroup →
        (subgroup.subgroupOf product).map productAutomorphism.toMonoidHom =
          subgroup.subgroupOf product := by
    intro subgroup hinvariant
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      have hmem := Subgroup.mem_map_of_mem automorphism.toMonoidHom hlift
      rwa [hinvariant] at hmem
    · intro hmem
      have hinverse : automorphism.symm element.val ∈ subgroup := by
        rw [← hinvariant] at hmem
        obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp hmem
        change automorphism lift = element.val at hvalue
        have heq : automorphism.symm element.val = lift := by rw [← hvalue]; simp
        exact heq ▸ hlift
      exact ⟨productAutomorphism.symm element, hinverse,
        productAutomorphism.apply_symm_apply element⟩
  have hlocalDerived := derived_fixed_of_cover localLeft localRight hlocalCommutator hlocalCover
    productAutomorphism (hlocalInvariant left hleftInvariant) (hlocalInvariant right hrightInvariant)
  have hfixedMap : (fixedSubgroup productAutomorphism).map product.subtype =
      product ⊓ fixedSubgroup automorphism := by
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact ⟨lift.property, congrArg Subtype.val hlift⟩
    · rintro ⟨hproduct, hfixed⟩
      exact ⟨⟨element, hproduct⟩, Subtype.ext hfixed, rfl⟩
  have hleftFixedMap : (localLeft ⊓ fixedSubgroup productAutomorphism).map product.subtype =
      left ⊓ fixedSubgroup automorphism := by
    rw [Subgroup.map_inf _ _ _ product.subtype_injective, hleftMap, hfixedMap]
    exact (inf_assoc left product (fixedSubgroup automorphism)).symm.trans
      (congrArg (fun subgroup : Subgroup G =>
      subgroup ⊓ fixedSubgroup automorphism) (inf_eq_left.mpr (le_sup_left : left ≤ product)))
  have hrightFixedMap : (localRight ⊓ fixedSubgroup productAutomorphism).map product.subtype =
      right ⊓ fixedSubgroup automorphism := by
    rw [Subgroup.map_inf _ _ _ product.subtype_injective, hrightMap, hfixedMap]
    exact (inf_assoc right product (fixedSubgroup automorphism)).symm.trans
      (congrArg (fun subgroup : Subgroup G =>
      subgroup ⊓ fixedSubgroup automorphism) (inf_eq_left.mpr (le_sup_right : right ≤ product)))
  have hmap := Subgroup.map_mono (f := product.subtype) hlocalDerived
  rwa [Subgroup.map_commutator, hfixedMap, Subgroup.map_sup,
    hleftFixedMap, hrightFixedMap] at hmap

end CFSG.ComponentClassification.FixedCommutingProduct
