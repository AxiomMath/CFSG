module

public import CFSG.LocalAnalysis.ComponentClassification.SwappedQuasisimpleProduct
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionOrbitDecomposition
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins

public section

open CFSG.Open

namespace CFSG.ComponentClassification.InvolutionOrbitComponentLocation

theorem finset_location {G : Type*} [Group G] [Finite G] {Index : Type*}
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (component : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism))
    (hcomponent : IsComponentOf component ⊤) (indices : Finset Index)
    (hstable : ∀ index ∈ indices, permutation index ∈ indices)
    (hcontained : component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤ indices.sup factors) :
    ∃ index ∈ indices, component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤
      factors index ⊔ factors (permutation index) := by
  classical
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  let image := component.map fixed.subtype
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  let : Group.IsPerfect image := Group.IsPerfect.map fixed.subtype
  revert hstable hcontained
  refine Finset.strongInductionOn indices ?_
  intro collection hinduction hstable hcontained
  by_cases hempty : collection = ∅
  · have hbot : image = ⊥ := by
      apply le_bot_iff.mp
      simpa only [hempty, Finset.sup_empty] using hcontained
    have hcomponentBot : component = ⊥ := by
      apply Subgroup.map_injective fixed.subtype_injective
      simpa only [Subgroup.map_bot] using hbot
    exact ((component.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hcomponent.2.2)) hcomponentBot).elim
  obtain ⟨index, hindex⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let pair : Finset Index := {index, permutation index}
  let remainder := collection \ pair
  have hpairMem : ∀ other, other ∈ pair ↔ other = index ∨ other = permutation index := by
    intro other
    simp only [pair, Finset.mem_insert, Finset.mem_singleton]
  have hpairSubset : pair ⊆ collection := by
    intro other hother
    rcases (hpairMem other).mp hother with rfl | rfl
    · exact hindex
    · exact hstable index hindex
  have hpairStable : ∀ other ∈ pair, permutation other ∈ pair := by
    intro other hother
    rcases (hpairMem other).mp hother with rfl | rfl
    · exact (hpairMem _).mpr (Or.inr rfl)
    · rw [hpermutation]
      exact (hpairMem _).mpr (Or.inl rfl)
  have hremainderStable : ∀ other ∈ remainder, permutation other ∈ remainder := by
    intro other hother
    obtain ⟨hcollection, hnotPair⟩ := Finset.mem_sdiff.mp hother
    refine Finset.mem_sdiff.mpr ⟨hstable other hcollection, ?_⟩
    intro himagePair
    rcases (hpairMem _).mp himagePair with heq | heq
    · have horiginal : other = permutation index :=
        (hpermutation other).symm.trans (congrArg permutation heq)
      exact hnotPair ((hpairMem _).mpr (Or.inr horiginal))
    · exact hnotPair ((hpairMem _).mpr (Or.inl (hpermutation.injective heq)))
  have hremainderSmaller : remainder ⊂ collection := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    have hmem : index ∈ remainder := heq.symm ▸ hindex
    exact (Finset.mem_sdiff.mp hmem).2 ((hpairMem _).mpr (Or.inl rfl))
  have hdisjoint : Disjoint pair remainder := by
    apply Finset.disjoint_left.mpr
    intro other hpair hremainder
    exact (Finset.mem_sdiff.mp hremainder).2 hpair
  have hcover : pair ∪ remainder = collection := by
    ext other
    constructor
    · intro hother
      rcases Finset.mem_union.mp hother with hpair | hremainder
      · exact hpairSubset hpair
      · exact (Finset.mem_sdiff.mp hremainder).1
    · intro hother
      by_cases hpair : other ∈ pair
      · exact Finset.mem_union.mpr (Or.inl hpair)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hother, hpair⟩))
  let left := pair.sup factors
  let right := remainder.sup factors
  have hleftCommutes : ⁅left, right⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    apply Finset.sup_le
    intro first hfirst
    apply Subgroup.le_centralizer_iff.mpr
    apply Finset.sup_le
    intro second hsecond
    apply Subgroup.le_centralizer_iff.mp
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    exact hcommutes (fun heq => Finset.disjoint_left.mp hdisjoint hfirst (heq ▸ hsecond))
  have hproductLe : image ≤ (left ⊔ right) ⊓ fixed := by
    apply le_inf
    · have hjoin : left ⊔ right = collection.sup factors := by
        rw [← Finset.sup_union, hcover]
      rwa [hjoin]
    · exact Subgroup.map_subtype_le _
  have hfixedCover : image ≤ (left ⊓ fixed) ⊔ (right ⊓ fixed) := by
    calc
      image = ⁅image, image⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(left ⊔ right) ⊓ fixed, (left ⊔ right) ⊓ fixed⁆ :=
        Subgroup.commutator_mono hproductLe hproductLe
      _ ≤ (left ⊓ fixed) ⊔ (right ⊓ fixed) :=
        FixedCommutingProduct.derived_fixed left right hleftCommutes automorphism
          (InvolutionOrbitDecomposition.finset_invariant factors permutation hpermutation automorphism
            himages pair hpairStable)
          (InvolutionOrbitDecomposition.finset_invariant factors permutation hpermutation automorphism
            himages remainder hremainderStable)
  let localLeft := (left ⊓ fixed).subgroupOf fixed
  let localRight := (right ⊓ fixed).subgroupOf fixed
  let : left.Normal := CenterlessCommutingFamily.finset_normal factors hnormal pair
  let : right.Normal := CenterlessCommutingFamily.finset_normal factors hnormal remainder
  let : localLeft.Normal := InvolutionDiagonal.fixed_factor_normal left automorphism
  let : localRight.Normal := InvolutionDiagonal.fixed_factor_normal right automorphism
  have hlocalCover : component ≤ localLeft ⊔ localRight := by
    apply (Subgroup.map_le_map_iff_of_injective fixed.subtype_injective).mp
    simpa only [Subgroup.map_sup, localLeft, localRight,
      Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem] using hfixedCover
  rcases OrdinaryComponentJoins.le_left_or_right component localLeft localRight hcomponent
    (Components.chain_of_mathlib_subnormal (inferInstance : localLeft.Normal).isSubnormal)
    (Components.chain_of_mathlib_subnormal (inferInstance : localRight.Normal).isSubnormal)
    hlocalCover with hleft | hright
  · refine ⟨index, hindex, ?_⟩
    have hleftLe : image ≤ left := by
      rintro member ⟨lift, hlift, rfl⟩
      exact (hleft hlift).1
    simpa only [left, pair, Finset.sup_insert, Finset.sup_singleton] using hleftLe
  · have hrestLe : image ≤ right := by
      rintro member ⟨lift, hlift, rfl⟩
      exact (hright hlift).1
    obtain ⟨other, hother, hle⟩ := hinduction remainder hremainderSmaller hremainderStable hrestLe
    exact ⟨other, (Finset.mem_sdiff.mp hother).1, hle⟩

theorem location {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (component : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism))
    (hcomponent : IsComponentOf component ⊤)
    (hcontained : component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤ ⨆ index, factors index) :
    ∃ index, component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤
      factors index ⊔ factors (permutation index) := by
  classical
  obtain ⟨index, _, hle⟩ := finset_location factors hnormal hcommutes permutation hpermutation
    automorphism himages component hcomponent Finset.univ (fun _ _ => Finset.mem_univ _)
    (by simpa only [Finset.sup_univ_eq_iSup] using hcontained)
  exact ⟨index, hle⟩

theorem invariant_or_diagonal {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hquasisimple : ∀ index, IsQuasisimple (factors index))
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (component : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism))
    (hcomponent : IsComponentOf component ⊤)
    (hcontained : component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤ ⨆ index, factors index) :
    ∃ index,
      ((factors index).map automorphism.toMonoidHom = factors index ∧
        component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤ factors index ∧
        IsComponentOf ((component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype).subgroupOf
          (factors index ⊓ FixedCommutingProduct.fixedSubgroup automorphism)) ⊤) ∨
      (∃ hfactorCommutes : ⁅factors index, (factors index).map automorphism.toMonoidHom⁆ = ⊥,
        (factors index).map automorphism.toMonoidHom ≠ factors index ∧
        component.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype =
          (InvolutionDiagonal.homomorphism (factors index) automorphism hfactorCommutes).range) := by
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  let image := component.map fixed.subtype
  have himageFixed : image ≤ fixed := Subgroup.map_subtype_le _
  have himageComponent : IsComponentOf (image.subgroupOf fixed) ⊤ :=
    OrdinaryComponentTransport.subtype_image_component fixed component hcomponent
  obtain ⟨index, hlocation⟩ := location factors hnormal hcommutes permutation hpermutation
    automorphism himages component hcomponent hcontained
  refine ⟨index, ?_⟩
  by_cases hfixedIndex : permutation index = index
  · have hle : image ≤ factors index := by
      simpa only [hfixedIndex, sup_idem] using hlocation
    refine Or.inl ⟨(himages index).trans (congrArg factors hfixedIndex), hle, ?_⟩
    exact OrdinaryComponentTransport.restrict_nested image (factors index ⊓ fixed) fixed
      (le_inf hle himageFixed) inf_le_right himageComponent
  · have hfactorCommutes : ⁅factors index, (factors index).map automorphism.toMonoidHom⁆ = ⊥ := by
      rw [himages]
      exact hcommutes (Ne.symm hfixedIndex)
    have hfactorDifferent : (factors index).map automorphism.toMonoidHom ≠ factors index := by
      intro heq
      have hselfCommutes := hfactorCommutes
      rw [heq] at hselfCommutes
      let : Group.IsPerfect (factors index) := ⟨(hquasisimple index).1⟩
      rw [Subgroup.commutator_eq_self] at hselfCommutes
      exact ((factors index).nontrivial_iff_ne_bot.mp
        (Quasisimple.nontrivial (hquasisimple index))) hselfCommutes
    refine Or.inr ⟨hfactorCommutes, hfactorDifferent, ?_⟩
    let product := factors index ⊔ (factors index).map automorphism.toMonoidHom
    let productFixed := product ⊓ fixed
    have himageProduct : image ≤ productFixed := by
      apply le_inf _ himageFixed
      change image ≤ factors index ⊔ (factors index).map automorphism.toMonoidHom
      rwa [himages]
    let : (factors index).Normal := hnormal index
    let : ((factors index).map automorphism.toMonoidHom).Normal :=
      (hnormal index).map automorphism.toMonoidHom automorphism.surjective
    let : product.Normal := Subgroup.sup_normal _ _
    let : (productFixed.subgroupOf fixed).Normal :=
      InvolutionDiagonal.fixed_factor_normal product automorphism
    let diagonal := InvolutionDiagonal.homomorphism (factors index) automorphism hfactorCommutes
    have hdiagonalProduct := SwappedQuasisimpleProduct.diagonal_le_fixed
      (factors index) automorphism hinvolutive hfactorCommutes
    have hdiagonalComponent := OrdinaryComponentTransport.extend_nested diagonal.range productFixed fixed
      hdiagonalProduct inf_le_right
      (inferInstance : (productFixed.subgroupOf fixed).Normal).isSubnormal
      (SwappedQuasisimpleProduct.diagonal_component_of_product_fixed
        (factors index) (hquasisimple index) automorphism hinvolutive hfactorCommutes)
    let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
    let : Group.IsPerfect image := Group.IsPerfect.map fixed.subtype
    have himageDiagonal : image ≤ diagonal.range := by
      calc
        image = ⁅image, image⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅productFixed, productFixed⁆ := Subgroup.commutator_mono himageProduct himageProduct
        _ = diagonal.range := SwappedQuasisimpleProduct.derived_product_fixed_eq_diagonal
          (factors index) (hquasisimple index) automorphism hinvolutive hfactorCommutes
    have heq := LocalComponents.eq_of_le _ _ himageComponent hdiagonalComponent
      (Subgroup.comap_mono himageDiagonal)
    have hmap := congrArg (Subgroup.map fixed.subtype) heq
    have hdiagonalFixed : diagonal.range ≤ fixed := hdiagonalProduct.trans inf_le_right
    rw [Subgroup.map_subgroupOf_eq_of_le himageFixed,
      Subgroup.map_subgroupOf_eq_of_le hdiagonalFixed] at hmap
    exact hmap

end CFSG.ComponentClassification.InvolutionOrbitComponentLocation
