module

public import CFSG.LocalAnalysis.ComponentClassification.LocalB
public import CFSG.LocalAnalysis.ComponentClassification.BlockFusion
public import CFSG.LocalAnalysis.ComponentClassification.BlockComplementInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CommonCentralizerComponent
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryLocalPumpUp

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockExternalInvolution

theorem fixes_factors {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hB : LocalB.LocalBProperty G) (element : G)
    (helement : element ∈ BlockFusion.involutions component) (actor : G)
    (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (himage : (MulAut.conj actor) element ∈ UniversalOrbitBlock.normalizer component)
    [Group.IsSolvable (componentClassificationOddCore (Subgroup.centralizer {(MulAut.conj actor) element}))]
    (houter : ∀ factor : Subgroup ((Subgroup.centralizer {(MulAut.conj actor) element}) ⧸
        componentClassificationOddCore (Subgroup.centralizer {(MulAut.conj actor) element})),
      IsComponentOf factor ⊤ → factor ≠ ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    ∀ factor ∈ UniversalOrbitBlock.block component,
      UniversalOrbitBlock.conjugate factor ((MulAut.conj actor) element) = factor := by
  classical
  let movedElement := (MulAut.conj actor) element
  let centralizer := Subgroup.centralizer {movedElement}
  let generated := UniversalOrbitBlock.generated component
  let normalizer := UniversalOrbitBlock.normalizer component
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have helementOrder : orderOf element = 2 := helement.1
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  have hmovedOrder : orderOf movedElement = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective element).trans helement.1
  have hmovedSquare : movedElement * movedElement = 1 := by
    rw [← pow_two, ← hmovedOrder]
    exact pow_orderOf_eq_one movedElement
  have hautomorphism : Function.Involutive (MulAut.conj movedElement) := by
    intro member
    have hconjSquare : MulAut.conj movedElement * MulAut.conj movedElement = 1 := by
      rw [← map_mul, hmovedSquare, map_one]
    exact congrArg (fun automorphism : MulAut G => automorphism member) hconjSquare
  have hfixedEq : FixedCommutingProduct.fixedSubgroup (MulAut.conj movedElement) = centralizer := by
    ext member
    change movedElement * member * movedElement⁻¹ = member ↔ member ∈ Subgroup.centralizer {movedElement}
    constructor
    · intro hfixed
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc
        member * movedElement = (movedElement * member * movedElement⁻¹) * movedElement := by rw [hfixed]
        _ = movedElement * member := by group
    · intro hcentral
      have hcommute := Subgroup.mem_centralizer_singleton_iff.mp hcentral
      rw [← hcommute, mul_inv_cancel_right]
  intro factor hfactor
  by_contra hdifferent
  let partner := UniversalOrbitBlock.conjugate factor movedElement
  have hpartner : partner ∈ UniversalOrbitBlock.block component :=
    (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple movedElement).mp
      himage factor hfactor
  have hfactorQuasi := UniversalOrbitBlock.orbit_quasisimple component hquasisimple factor hfactor.1
  have hfactorEven := UniversalOrbitBlock.orbit_even component heven factor hfactor.1
  have hfactorCommutes : ⁅factor, factor.map (MulAut.conj movedElement).toMonoidHom⁆ = ⊥ :=
    UniversalOrbitBlock.block_commutes component heven huniversal factor hfactor partner hpartner (Ne.symm hdifferent)
  let product := factor ⊔ partner
  let diagonal := InvolutionDiagonal.homomorphism factor (MulAut.conj movedElement) hfactorCommutes
  let diagonalSubgroup := diagonal.range
  have hdiagonalQuasi : IsQuasisimple diagonalSubgroup :=
    SwappedQuasisimpleProduct.diagonal_quasisimple factor hfactorQuasi (MulAut.conj movedElement) hfactorCommutes
  have hdiagonalEven : Even (Nat.card diagonalSubgroup) :=
    SwappedQuasisimpleProduct.diagonal_even factor hfactorQuasi hfactorEven (MulAut.conj movedElement) hfactorCommutes
  have hdiagonalLe : diagonalSubgroup ≤ product ⊓ centralizer := by
    have hle := SwappedQuasisimpleProduct.diagonal_le_fixed factor (MulAut.conj movedElement)
      hautomorphism hfactorCommutes
    rwa [hfixedEq] at hle
  obtain ⟨fixedInvolution, hfixedOrder, hfixedM, hfixedCentralizer, hfixedProduct, hfixedCentralizerLe⟩ :=
    BlockComplementInvolution.exists_fixed component heven huniversal hquasisimple hcard
      movedElement hmovedOrder himage factor hfactor
  let firstFixed := Subgroup.centralizer {fixedInvolution}
  have hfactorM : factor ≤ generated := CommutingComponentFamily.factor_le _ factor hfactor
  have hpartnerM : partner ≤ generated := CommutingComponentFamily.factor_le _ partner hpartner
  have hproductM : product ≤ generated := sup_le hfactorM hpartnerM
  have hproductNormal : (product.subgroupOf generated).Normal := by
    let : (factor.subgroupOf generated).Normal :=
      UniversalOrbitBlock.factor_normal component heven huniversal factor hfactor
    let : (partner.subgroupOf generated).Normal :=
      UniversalOrbitBlock.factor_normal component heven huniversal partner hpartner
    rw [Subgroup.subgroupOf_sup hfactorM hpartnerM]
    infer_instance
  have hgeneratedNormal : (generated.subgroupOf normalizer).Normal := by
    change (generated.subgroupOf (Subgroup.normalizer (generated : Set G))).Normal
    infer_instance
  have hproductFirstFixed : product ≤ firstFixed := by
    intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hfixedProduct member hmember)
  have hderived : ⁅product ⊓ centralizer, product ⊓ centralizer⁆ = diagonalSubgroup := by
    have heq := SwappedQuasisimpleProduct.derived_product_fixed_eq_diagonal factor hfactorQuasi
      (MulAut.conj movedElement) hautomorphism hfactorCommutes
    rwa [hfixedEq] at heq
  have hcommonComponent := CommonCentralizerComponent.derived_component product generated normalizer
    firstFixed centralizer hproductM Subgroup.le_normalizer hproductNormal hgeneratedNormal
    hfixedCentralizerLe hproductFirstFixed diagonalSubgroup hdiagonalQuasi hderived
  have hcommonComponent' : IsComponentOf (diagonalSubgroup.subgroupOf (centralizer ⊓ firstFixed)) ⊤ := by
    rwa [inf_comm] at hcommonComponent
  have hlocalComponent := OrdinaryComponentTransport.common_centralizer_transport diagonalSubgroup centralizer
    fixedInvolution hfixedCentralizer hcommonComponent'
  have hdiagonalCentral : diagonalSubgroup.subgroupOf centralizer ≤
      Subgroup.centralizer {(⟨fixedInvolution, hfixedCentralizer⟩ : centralizer)} := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hproductFirstFixed (hdiagonalLe hmember).1)
  have hlocalOrder : orderOf (⟨fixedInvolution, hfixedCentralizer⟩ : centralizer) = 2 :=
    (orderOf_injective centralizer.subtype centralizer.subtype_injective _).symm.trans hfixedOrder
  have hlocalLayer := OrdinaryLocalPumpUp.enters_layer_of_proper_outer
    (fun candidate hcandidate => LocalB.ordinary_at_involution hB movedElement hmovedOrder candidate hcandidate)
    (⟨fixedInvolution, hfixedCentralizer⟩ : centralizer) hlocalOrder
    (diagonalSubgroup.subgroupOf centralizer) hdiagonalCentral hlocalComponent houter
  obtain ⟨_, anchorFactor, hanchorFactor, hanchorCentral⟩ := helement
  have hcentralizerLe : centralizer ≤ normalizer.map (MulAut.conj actor).toMonoidHom := by
    have hle := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
      (UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple
        anchorFactor hanchorFactor element helementOrder hanchorCentral)
    rwa [UniversalComponentBlock.singleton_centralizer_map] at hle
  let factors : Index → Subgroup G := fun index => UniversalOrbitBlock.conjugate index.val actor
  have hfamilyInjective : Function.Injective factors := by
    intro first second heq
    apply Subtype.ext
    exact Subgroup.map_injective (f := (MulAut.conj actor).toMonoidHom) (MulAut.conj actor).injective heq
  have hfamilyCommutes : Pairwise (fun first second : Index => ⁅factors first, factors second⁆ = ⊥) := by
    intro first second hne
    have hcommutes := UniversalOrbitBlock.block_commutes component heven huniversal first.val first.property
      second.val second.property (fun heq => hne (Subtype.ext heq))
    have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom) hcommutes
    change ⁅first.val.map (MulAut.conj actor).toMonoidHom,
      second.val.map (MulAut.conj actor).toMonoidHom⁆ = ⊥
    simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap
  let anchor : Index := ⟨anchorFactor, hanchorFactor⟩
  have hanchorLe : factors anchor ≤ centralizer := by
    have hle := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
      (UniversalComponentBlock.component_le_involution_centralizer anchorFactor element hanchorCentral)
    rwa [UniversalComponentBlock.singleton_centralizer_map] at hle
  have hanchor : IsComponentOf ((factors anchor).subgroupOf centralizer) ⊤ := by
    have hlocal := OrdinaryComponentTransport.map_nested (MulAut.conj actor) anchorFactor
      (Subgroup.centralizer {element})
      (UniversalOrbitBlock.orbit_universal component huniversal anchorFactor hanchorFactor.1
        element helementOrder hanchorCentral)
    rwa [UniversalComponentBlock.singleton_centralizer_map] at hlocal
  have hpreserves : ∀ index : Index, ∃ imageIndex,
      (factors index).map (MulAut.conj fixedInvolution).toMonoidHom = factors imageIndex := by
    obtain ⟨preimage, hpreimage, hpreimageEq⟩ := Subgroup.mem_map.mp (hcentralizerLe hfixedCentralizer)
    have hmultiply : fixedInvolution * actor = actor * preimage := by
      change actor * preimage * actor⁻¹ = fixedInvolution at hpreimageEq
      rw [← hpreimageEq]
      group
    intro index
    have hpreserved := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal
      hquasisimple preimage).mp hpreimage index.val index.property
    refine ⟨⟨UniversalOrbitBlock.conjugate index.val preimage, hpreserved⟩, ?_⟩
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate index.val actor) fixedInvolution =
      UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate index.val preimage) actor
    rw [UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate, hmultiply]
  have hfixedSquare : (⟨fixedInvolution, hfixedCentralizer⟩ : centralizer) *
      (⟨fixedInvolution, hfixedCentralizer⟩ : centralizer) = 1 := by
    apply Subtype.ext
    change fixedInvolution * fixedInvolution = 1
    rw [← pow_two, ← hfixedOrder]
    exact pow_orderOf_eq_one fixedInvolution
  obtain ⟨centralizedIndex, hcentralized⟩ := ComponentFamilyPumpUpFusion.of_local_layer factors
    hfamilyInjective hfamilyCommutes hfamilyCard centralizer anchor hanchorLe hanchor
    (⟨fixedInvolution, hfixedCentralizer⟩ : centralizer) hfixedSquare hpreserves diagonalSubgroup
    (hdiagonalLe.trans inf_le_right) hdiagonalCentral hlocalComponent hlocalLayer
  let firstIndex : Index := ⟨factor, hfactor⟩
  let secondIndex : Index := ⟨partner, hpartner⟩
  obtain ⟨outside, houtsideFirst, houtsideSecond⟩ := ComponentFamilyPumpUpFusion.exists_outside_two
    hfamilyCard firstIndex secondIndex
  have hproductCentralizes : product ≤ Subgroup.centralizer (outside.val : Set G) := by
    apply sup_le
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (UniversalOrbitBlock.block_commutes component heven huniversal factor hfactor outside.val outside.property
          (fun heq => houtsideFirst (Subtype.ext heq.symm)))
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (UniversalOrbitBlock.block_commutes component heven huniversal partner hpartner outside.val outside.property
          (fun heq => houtsideSecond (Subtype.ext heq.symm)))
  obtain ⟨diagonalInvolution, hdiagonalOrder⟩ := exists_prime_orderOf_dvd_card'
    (G := diagonalSubgroup) 2 (even_iff_two_dvd.mp hdiagonalEven)
  have hambientDiagonalOrder : orderOf diagonalInvolution.val = 2 :=
    (orderOf_injective diagonalSubgroup.subtype diagonalSubgroup.subtype_injective diagonalInvolution).trans hdiagonalOrder
  have hnormalizes := BlockFusion.common_involution_forces_normalizer component heven huniversal hquasisimple
    centralizedIndex.val outside.val centralizedIndex.property outside.property actor diagonalInvolution.val
    hambientDiagonalOrder
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralized diagonalInvolution.property)
    (hproductCentralizes (hdiagonalLe diagonalInvolution.property).1)
  exact hactor hnormalizes

end CFSG.ComponentClassification.BlockExternalInvolution
