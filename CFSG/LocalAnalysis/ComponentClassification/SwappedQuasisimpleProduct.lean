module

public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SwappedQuasisimpleProduct

theorem diagonal_kernel_central {G : Type*} [Group G] (factor : Subgroup G)
    (automorphism : MulAut G) (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    (InvolutionDiagonal.homomorphism factor automorphism hcommutes).ker ≤ Subgroup.center factor := by
  intro member hmember
  have hone : member.val * automorphism member.val = 1 := MonoidHom.mem_ker.mp hmember
  have hmemberImage : member.val ∈ factor.map automorphism.toMonoidHom := by
    have heq : member.val = (automorphism member.val)⁻¹ := mul_eq_one_iff_eq_inv.mp hone
    rw [heq]
    exact (factor.map automorphism.toMonoidHom).inv_mem
      (Subgroup.mem_map_of_mem automorphism.toMonoidHom member.property)
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes other.property)
      member.val hmemberImage).symm

theorem diagonal_quasisimple {G : Type*} [Group G] (factor : Subgroup G)
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    IsQuasisimple (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
  let diagonal := InvolutionDiagonal.homomorphism factor automorphism hcommutes
  have hkernel := diagonal_kernel_central factor automorphism hcommutes
  have hquasiQuotient := Quasisimple.central_quotient hquasisimple diagonal.ker hkernel
  exact Components.quasisimple_of_equiv (QuotientGroup.quotientKerEquivRange diagonal).symm hquasiQuotient

theorem diagonal_le_fixed {G : Type*} [Group G] (factor : Subgroup G)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range ≤
      (factor ⊔ factor.map automorphism.toMonoidHom) ⊓ FixedCommutingProduct.fixedSubgroup automorphism := by
  rintro member ⟨lift, rfl⟩
  change lift.val * automorphism lift.val ∈
    (factor ⊔ factor.map automorphism.toMonoidHom) ⊓ FixedCommutingProduct.fixedSubgroup automorphism
  refine ⟨Subgroup.mul_mem_sup lift.property
    (Subgroup.mem_map_of_mem automorphism.toMonoidHom lift.property), ?_⟩
  change automorphism (lift.val * automorphism lift.val) = lift.val * automorphism lift.val
  rw [map_mul, hinvolutive]
  exact Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes lift.property)
      (automorphism lift.val) (Subgroup.mem_map_of_mem automorphism.toMonoidHom lift.property)

noncomputable def diagonal_center_quotient_equivalence {G : Type*} [Group G]
    (factor : Subgroup G) (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    factor ⧸ Subgroup.center factor ≃*
      (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range ⧸
        Subgroup.center (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
  let diagonal := InvolutionDiagonal.homomorphism factor automorphism hcommutes
  let : Group.IsPerfect factor := ⟨hquasisimple.1⟩
  apply PerfectCentralQuotient.equivalence diagonal.rangeRestrict diagonal.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict]
  exact diagonal_kernel_central factor automorphism hcommutes

theorem diagonal_even {G : Type*} [Group G] [Finite G] (factor : Subgroup G)
    (hquasisimple : IsQuasisimple factor) (heven : Even (Nat.card factor))
    (automorphism : MulAut G) (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    Even (Nat.card (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range) := by
  let diagonal := InvolutionDiagonal.homomorphism factor automorphism hcommutes
  let : Group.IsPerfect factor := ⟨hquasisimple.1⟩
  apply PerfectCentralQuotient.even_image diagonal.rangeRestrict diagonal.rangeRestrict_surjective _ heven
  rw [MonoidHom.ker_rangeRestrict]
  exact diagonal_kernel_central factor automorphism hcommutes

theorem fixed_eq_diagonal_sup_central {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤) :
    FixedCommutingProduct.fixedSubgroup automorphism =
      (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range ⊔
        ((factor ⊓ factor.map automorphism.toMonoidHom) ⊓
          FixedCommutingProduct.fixedSubgroup automorphism) := by
  let partner := factor.map automorphism.toMonoidHom
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  have hcentral := FixedCommutingProduct.inf_le_center factor partner hcommutes hcover
  apply le_antisymm
  · intro member hmember
    have hproduct : member ∈ factor ⊔ partner := by rw [hcover]; exact Subgroup.mem_top _
    obtain ⟨first, hfirst, second, hsecond, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hproduct
    have hsecondImage : automorphism second ∈ factor := by
      obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hsecond
      change automorphism (automorphism original) ∈ factor
      rw [hinvolutive]
      exact horiginal
    have hfirstImage : automorphism first ∈ partner :=
      Subgroup.mem_map_of_mem automorphism.toMonoidHom hfirst
    have hfixed : automorphism first * automorphism second = first * second :=
      (map_mul automorphism first second).symm.trans hmember
    have hcommute : automorphism first * automorphism second = automorphism second * automorphism first :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hsecondImage)
          (automorphism first) hfirstImage
    let central := first⁻¹ * automorphism second
    have hcentralEq : central = second * (automorphism first)⁻¹ := by
      have heq := hcommute.symm.trans hfixed
      calc
        central = first⁻¹ * (automorphism second * automorphism first) * (automorphism first)⁻¹ := by
          dsimp [central]
          group
        _ = second * (automorphism first)⁻¹ := by rw [heq]; group
    have hcentralIntersection : central ∈ factor ⊓ partner :=
      ⟨factor.mul_mem (factor.inv_mem hfirst) hsecondImage,
        by rw [hcentralEq]; exact partner.mul_mem hsecond (partner.inv_mem hfirstImage)⟩
    have hcentralCenter := hcentral hcentralIntersection
    have hsecondEq : second = automorphism first * central := by
      have heq : central * automorphism first = second := by rw [hcentralEq]; group
      exact (((Subgroup.mem_center_iff.mp hcentralCenter) (automorphism first)).trans heq).symm
    have hcentralFixed : automorphism central = central := by
      have hfirstEq : automorphism second = first * central := by dsimp [central]; group
      have hmap := congrArg automorphism hsecondEq
      rw [map_mul, hinvolutive, hfirstEq] at hmap
      exact mul_left_cancel hmap.symm
    have hdiagonal : first * automorphism first ∈
        (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range :=
      ⟨⟨first, hfirst⟩, rfl⟩
    have hcentralMembership : central ∈ (factor ⊓ partner) ⊓ fixed :=
      ⟨hcentralIntersection, hcentralFixed⟩
    have hmem := Subgroup.mul_mem_sup hdiagonal hcentralMembership
    rwa [mul_assoc, ← hsecondEq] at hmem
  · apply sup_le
    · exact (diagonal_le_fixed factor automorphism hinvolutive hcommutes).trans inf_le_right
    · exact inf_le_right

theorem derived_fixed_eq_diagonal {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤) :
    ⁅FixedCommutingProduct.fixedSubgroup automorphism, FixedCommutingProduct.fixedSubgroup automorphism⁆ =
      (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
  have hcentral : (factor ⊓ factor.map automorphism.toMonoidHom) ⊓
      FixedCommutingProduct.fixedSubgroup automorphism ≤ Subgroup.center G :=
    inf_le_left.trans (FixedCommutingProduct.inf_le_center factor _ hcommutes hcover)
  let : ((factor ⊓ factor.map automorphism.toMonoidHom) ⊓
      FixedCommutingProduct.fixedSubgroup automorphism).Normal := by
    constructor
    intro member hmember actor
    have hcommute := (Subgroup.mem_center_iff.mp (hcentral hmember)) actor
    simpa [← mul_assoc, hcommute] using hmember
  rw [fixed_eq_diagonal_sup_central factor automorphism hinvolutive hcommutes hcover]
  rw [CentralExtensions.commutator_sup_central _ _ hcentral]
  let : Group.IsPerfect factor := ⟨hquasisimple.1⟩
  let : Group.IsPerfect (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range :=
    Group.IsPerfect.range _
  exact Subgroup.commutator_eq_self

theorem diagonal_normal_in_fixed {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤) :
    ((InvolutionDiagonal.homomorphism factor automorphism hcommutes).range.subgroupOf
      (FixedCommutingProduct.fixedSubgroup automorphism)).Normal := by
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  have hnormal : (⁅fixed, fixed⁆.subgroupOf (fixed ⊔ fixed)).Normal := inferInstance
  rw [show fixed ⊔ fixed = fixed from sup_idem fixed] at hnormal
  change (⁅FixedCommutingProduct.fixedSubgroup automorphism,
    FixedCommutingProduct.fixedSubgroup automorphism⁆.subgroupOf
      (FixedCommutingProduct.fixedSubgroup automorphism)).Normal at hnormal
  rwa [derived_fixed_eq_diagonal factor hquasisimple automorphism hinvolutive hcommutes hcover] at hnormal

theorem diagonal_component_of_fixed {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤) :
    IsComponentOf ((InvolutionDiagonal.homomorphism factor automorphism hcommutes).range.subgroupOf
      (FixedCommutingProduct.fixedSubgroup automorphism)) ⊤ := by
  apply (OrdinaryComponentTransport.subgroupOf_iff _ _
    ((diagonal_le_fixed factor automorphism hinvolutive hcommutes).trans inf_le_right)).mpr
  exact ⟨(diagonal_normal_in_fixed factor hquasisimple automorphism hinvolutive hcommutes hcover).isSubnormal,
    diagonal_quasisimple factor hquasisimple automorphism hcommutes⟩

theorem fixed_derived_image {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤) :
    (commutator (FixedCommutingProduct.fixedSubgroup automorphism)).map
      (FixedCommutingProduct.fixedSubgroup automorphism).subtype =
        (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
  change Subgroup.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype
    (⁅⊤, ⊤⁆ : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism)) = _
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact derived_fixed_eq_diagonal factor hquasisimple automorphism hinvolutive hcommutes hcover

theorem fixed_layer_image {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤) :
    (Layer.subgroup (FixedCommutingProduct.fixedSubgroup automorphism)).map
      (FixedCommutingProduct.fixedSubgroup automorphism).subtype =
        (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
  apply le_antisymm
  · rw [← fixed_derived_image factor hquasisimple automorphism hinvolutive hcommutes hcover]
    exact Subgroup.map_mono (Layer.le_derived _)
  · have hcomponent := diagonal_component_of_fixed factor hquasisimple automorphism
      hinvolutive hcommutes hcover
    have hmap := Subgroup.map_mono (f := (FixedCommutingProduct.fixedSubgroup automorphism).subtype)
      (Layer.component_le hcomponent)
    rwa [Subgroup.map_subgroupOf_eq_of_le
      ((diagonal_le_fixed factor automorphism hinvolutive hcommutes).trans inf_le_right)] at hmap

theorem unique_fixed_component {G : Type*} [Group G] (factor : Subgroup G) [factor.Normal]
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥)
    (hcover : factor ⊔ factor.map automorphism.toMonoidHom = ⊤)
    (component : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism))
    (hcomponent : IsComponentOf component ⊤) :
    component = (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range.subgroupOf
      (FixedCommutingProduct.fixedSubgroup automorphism) := by
  apply LocalComponents.eq_of_le _ _ hcomponent
    (diagonal_component_of_fixed factor hquasisimple automorphism hinvolutive hcommutes hcover)
  have hmap := Subgroup.map_mono (f := (FixedCommutingProduct.fixedSubgroup automorphism).subtype)
    (Layer.component_le hcomponent)
  rw [fixed_layer_image factor hquasisimple automorphism hinvolutive hcommutes hcover] at hmap
  exact Subgroup.map_le_iff_le_comap.mp hmap

theorem product_invariant {G : Type*} [Group G] (factor : Subgroup G)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism) :
    (factor ⊔ factor.map automorphism.toMonoidHom).map automorphism.toMonoidHom =
      factor ⊔ factor.map automorphism.toMonoidHom := by
  have hsquare : automorphism.toMonoidHom.comp automorphism.toMonoidHom = MonoidHom.id G := by
    ext member
    exact hinvolutive member
  rw [Subgroup.map_sup, Subgroup.map_map, hsquare, Subgroup.map_id, sup_comm]

@[expose] noncomputable def productAutomorphism {G : Type*} [Group G] (factor : Subgroup G)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism) :
    MulAut ↥(factor ⊔ factor.map automorphism.toMonoidHom) :=
  (automorphism.subgroupMap (factor ⊔ factor.map automorphism.toMonoidHom)).trans
    (MulEquiv.subgroupCongr (product_invariant factor automorphism hinvolutive))

theorem derived_product_fixed_eq_diagonal {G : Type*} [Group G] (factor : Subgroup G)
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    ⁅(factor ⊔ factor.map automorphism.toMonoidHom) ⊓ FixedCommutingProduct.fixedSubgroup automorphism,
      (factor ⊔ factor.map automorphism.toMonoidHom) ⊓ FixedCommutingProduct.fixedSubgroup automorphism⁆ =
      (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
  let product := factor ⊔ factor.map automorphism.toMonoidHom
  let localAutomorphism := productAutomorphism factor automorphism hinvolutive
  let localFactor := factor.subgroupOf product
  let localPartner := (factor.map automorphism.toMonoidHom).subgroupOf product
  have hfactorMap : localFactor.map product.subtype = factor :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hpartnerMap : localPartner.map product.subtype = factor.map automorphism.toMonoidHom :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hlocalImage : localFactor.map localAutomorphism.toMonoidHom = localPartner := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hlift
    · intro hmember
      obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmember
      exact ⟨⟨original, (le_sup_left : factor ≤ product) horiginal⟩, horiginal, Subtype.ext heq⟩
  have hlocalCommutes : ⁅localFactor, localFactor.map localAutomorphism.toMonoidHom⁆ = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ product.subtype_injective).mp
    rw [Subgroup.map_commutator, hlocalImage, hfactorMap, hpartnerMap]
    exact hcommutes
  let : localFactor.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    apply sup_le Subgroup.le_normalizer
    exact (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hlocalCover : localFactor ⊔ localFactor.map localAutomorphism.toMonoidHom = ⊤ := by
    apply Subgroup.map_injective product.subtype_injective
    rw [Subgroup.map_sup, hlocalImage, hfactorMap, hpartnerMap,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hlocalQuasi : IsQuasisimple localFactor :=
    Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left) hquasisimple
  have hlocalInvolutive : Function.Involutive localAutomorphism := by
    intro member
    exact Subtype.ext (hinvolutive member.val)
  have hlocalDerived := derived_fixed_eq_diagonal localFactor hlocalQuasi localAutomorphism
    hlocalInvolutive hlocalCommutes hlocalCover
  have hfixedMap : (FixedCommutingProduct.fixedSubgroup localAutomorphism).map product.subtype =
      product ⊓ FixedCommutingProduct.fixedSubgroup automorphism := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact ⟨lift.property, congrArg Subtype.val hlift⟩
    · rintro ⟨hproduct, hfixed⟩
      exact ⟨⟨member, hproduct⟩, Subtype.ext hfixed, rfl⟩
  have hdiagonalMap : (InvolutionDiagonal.homomorphism localFactor localAutomorphism hlocalCommutes).range.map
      product.subtype = (InvolutionDiagonal.homomorphism factor automorphism hcommutes).range := by
    ext member
    constructor
    · rintro ⟨lift, ⟨original, rfl⟩, rfl⟩
      exact ⟨⟨original.val.val, original.property⟩, rfl⟩
    · rintro ⟨original, rfl⟩
      exact ⟨_, ⟨⟨⟨original.val, (le_sup_left : factor ≤ product) original.property⟩,
        original.property⟩, rfl⟩, rfl⟩
  have hmap := congrArg (Subgroup.map product.subtype) hlocalDerived
  rwa [Subgroup.map_commutator, hfixedMap, hdiagonalMap] at hmap

theorem diagonal_normal_in_product_fixed {G : Type*} [Group G] (factor : Subgroup G)
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    ((InvolutionDiagonal.homomorphism factor automorphism hcommutes).range.subgroupOf
      ((factor ⊔ factor.map automorphism.toMonoidHom) ⊓
        FixedCommutingProduct.fixedSubgroup automorphism)).Normal := by
  let fixed := (factor ⊔ factor.map automorphism.toMonoidHom) ⊓
    FixedCommutingProduct.fixedSubgroup automorphism
  have hnormal : (⁅fixed, fixed⁆.subgroupOf (fixed ⊔ fixed)).Normal := inferInstance
  rw [show fixed ⊔ fixed = fixed from sup_idem fixed] at hnormal
  change (⁅(factor ⊔ factor.map automorphism.toMonoidHom) ⊓ FixedCommutingProduct.fixedSubgroup automorphism,
    (factor ⊔ factor.map automorphism.toMonoidHom) ⊓ FixedCommutingProduct.fixedSubgroup automorphism⁆.subgroupOf
      ((factor ⊔ factor.map automorphism.toMonoidHom) ⊓
        FixedCommutingProduct.fixedSubgroup automorphism)).Normal at hnormal
  rwa [derived_product_fixed_eq_diagonal factor hquasisimple automorphism hinvolutive hcommutes] at hnormal

theorem diagonal_component_of_product_fixed {G : Type*} [Group G] (factor : Subgroup G)
    (hquasisimple : IsQuasisimple factor) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ⁅factor, factor.map automorphism.toMonoidHom⁆ = ⊥) :
    IsComponentOf ((InvolutionDiagonal.homomorphism factor automorphism hcommutes).range.subgroupOf
      ((factor ⊔ factor.map automorphism.toMonoidHom) ⊓
        FixedCommutingProduct.fixedSubgroup automorphism)) ⊤ := by
  apply (OrdinaryComponentTransport.subgroupOf_iff _ _
    (diagonal_le_fixed factor automorphism hinvolutive hcommutes)).mpr
  exact ⟨(diagonal_normal_in_product_fixed factor hquasisimple automorphism hinvolutive hcommutes).isSubnormal,
    diagonal_quasisimple factor hquasisimple automorphism hcommutes⟩

end CFSG.ComponentClassification.SwappedQuasisimpleProduct
