module

public import CFSG.LocalAnalysis.ComponentClassification.ZStarQuasisimpleSylowInvolution

public section

open CFSG.Open

namespace CFSG.ComponentClassification.QuasisimpleInvolutionProduct

theorem centralizes {G : Type*} [Group G] [Finite G]
    (ambient : Subgroup G) (hquasisimple : IsQuasisimple ambient) (heven : Even (Nat.card ambient))
    (member : G) (horder : orderOf member = 2)
    (hnormalizes : member ∈ Subgroup.normalizer (ambient : Set G))
    (hdisjoint : Disjoint ambient (Subgroup.zpowers member))
    (fixed : Sylow 2 ambient)
    (hcentralizes : member ∈ Subgroup.centralizer
      (((fixed : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G))
    (hsquares : ∀ element ∈ (fixed : Subgroup ambient).map ambient.subtype,
      element ^ 2 = 1 → element ∈ (Subgroup.center ambient).map ambient.subtype) :
    member ∈ Subgroup.centralizer (ambient : Set G) := by
  let cyclic := Subgroup.zpowers member
  let product := ambient ⊔ cyclic
  let localAmbient := ambient.subgroupOf product
  let : localAmbient.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hnormalizes))
  let equivalence : localAmbient ≃* ambient := Subgroup.subgroupOfEquivOfLe (le_sup_left : ambient ≤ product)
  have hlocalQuasisimple := Components.quasisimple_of_equiv equivalence hquasisimple
  have hlocalEven : Even (Nat.card localAmbient) := by
    rw [Nat.card_congr equivalence.toEquiv]
    exact heven
  let kernel := (Subgroup.center localAmbient).map localAmbient.subtype
  let : kernel.Normal := inferInstance
  have hkernelLe : kernel ≤ localAmbient := by
    rintro element ⟨lift, hlift, rfl⟩
    exact lift.property
  have hkernel : kernel.subgroupOf localAmbient = Subgroup.center localAmbient := by
    exact Subgroup.comap_map_eq_self_of_injective localAmbient.subtype_injective _
  have hkernelMap : kernel.map product.subtype = (Subgroup.center ambient).map ambient.subtype := by
    rw [Subgroup.map_map]
    have hhom : product.subtype.comp localAmbient.subtype = ambient.subtype.comp equivalence.toMonoidHom := by
      ext element
      rfl
    rw [hhom, ← Subgroup.map_map]
    have hcenter : (Subgroup.center localAmbient).map equivalence.toMonoidHom = Subgroup.center ambient := by
      apply le_antisymm
      · rintro element ⟨lift, hlift, rfl⟩
        apply Subgroup.mem_center_iff.mpr
        intro other
        obtain ⟨preimage, rfl⟩ := equivalence.surjective other
        exact congrArg equivalence (Subgroup.mem_center_iff.mp hlift preimage)
      · intro element helement
        apply Subgroup.mem_map.mpr
        refine ⟨equivalence.symm element, Subgroup.mem_center_iff.mpr ?_, equivalence.apply_symm_apply element⟩
        intro other
        apply equivalence.injective
        simpa only [map_mul, equivalence.apply_symm_apply] using Subgroup.mem_center_iff.mp helement (equivalence other)
    rw [hcenter]
  have hmemberProduct : member ∈ product := (le_sup_right : cyclic ≤ product) (Subgroup.mem_zpowers member)
  let localMember : product := ⟨member, hmemberProduct⟩
  have hlocalOrder : orderOf localMember = 2 :=
    (orderOf_injective product.subtype product.subtype_injective localMember).symm.trans horder
  have hlocalProduct : localAmbient ⊔ Subgroup.zpowers localMember = ⊤ := by
    apply Subgroup.map_injective product.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hlocalDisjoint : Disjoint localAmbient (Subgroup.zpowers localMember) := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro element helement
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hdisjoint.eq_bot ▸
      (show element.val ∈ ambient ⊓ cyclic from ⟨helement.1, by
        change element.val ∈ cyclic
        have hmap : element.val ∈ (Subgroup.zpowers localMember).map product.subtype :=
          Subgroup.mem_map.mpr ⟨element, helement.2, rfl⟩
        rw [MonoidHom.map_zpowers] at hmap
        exact hmap⟩))
  let localFixed := fixed.mapSurjective (f := equivalence.symm.toMonoidHom)
    (show Function.Surjective equivalence.symm.toMonoidHom from equivalence.symm.surjective)
  have hfixedMap : ((localFixed : Subgroup localAmbient).map localAmbient.subtype).map product.subtype =
      (fixed : Subgroup ambient).map ambient.subtype := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hlocalCentral : localMember ∈ Subgroup.centralizer
      (((localFixed : Subgroup localAmbient).map localAmbient.subtype : Subgroup product) : Set product) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    apply Subtype.ext
    apply Subgroup.mem_centralizer_iff.mp hcentralizes element.val
    rw [← hfixedMap]
    exact Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
  have hlocalSquares : ∀ element ∈ (localFixed : Subgroup localAmbient).map localAmbient.subtype,
      element ^ 2 = 1 → element ∈ kernel := by
    intro element helement hsquare
    have houterMember : element.val ∈ (fixed : Subgroup ambient).map ambient.subtype := by
      rw [← hfixedMap]
      exact Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
    have houterSquare : element.val ^ 2 = 1 := congrArg Subtype.val hsquare
    have houterKernel := hsquares element.val houterMember houterSquare
    rw [← hkernelMap] at houterKernel
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp houterKernel
    have heqLocal : lift = element := Subtype.ext heq
    exact heqLocal ▸ hlift
  have hquotientCentral := ZStarQuasisimpleSylowInvolution.centralizes_quotient localAmbient kernel hlocalQuasisimple
    hlocalEven hkernelLe hkernel localMember hlocalOrder hlocalProduct hlocalDisjoint localFixed hlocalCentral hlocalSquares
  have hlocalCentralizes := ZStarQuasisimpleSylowInvolution.centralizes_ambient localAmbient kernel hlocalQuasisimple.1
    hkernel localMember hquotientCentral
  apply Subgroup.mem_centralizer_iff.mpr
  intro element helement
  have hproductMember : element ∈ product := (le_sup_left : ambient ≤ product) helement
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hlocalCentralizes
    (⟨element, hproductMember⟩ : product) helement)

end CFSG.ComponentClassification.QuasisimpleInvolutionProduct
